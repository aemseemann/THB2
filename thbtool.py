from __future__ import annotations

import os
import sys
from enum import IntEnum, Enum, IntFlag
import re
import functools
from pathlib import Path
from datetime import datetime, timezone
import struct
import math

from typing import Any, Annotated, Self
from collections.abc import Iterator, Callable, Buffer, Mapping

import click
from types import SimpleNamespace
from zlib import crc32

import pydantic
import yaml
from dataclasses import dataclass
from contextlib import nullcontext

import asyncio

from bleak import BleakClient
from bleak.exc import BleakCharacteristicNotFoundError, BleakError


OTA_UUID = "FFF3"
CMD_UUID = "FFF4"

# Service UUID: 0x180F
BAT_UUID = "2A19"
# Service UUID: 0x181A (ENV_SENSING_SERV_UUID)
TEMP_UUID = "2A6E"
HUMID_UUID = "2A6F"

REBOOT_CODE_OTA = 0x33

class Features(Enum):
    OTA = 0x00000001
    OTA_EXT = 0x00000002
    PINCODE = 0x00000004
    BINDKEY = 0x00000008
    HISTORY = 0x00000010
    SCREEN = 0x00000020
    LE_LR = 0x00000040
    THS = 0x00000080
    RDS = 0x00000100
    KEY = 0x00000200
    OUTS = 0x00000400
    INS = 0x00000800
    TIME_ADJUST = 0x00001000
    HARD_CLOCK = 0x00002000
    TH_TRG = 0x00004000
    LED =  0x00008000
    MI_KEYS = 0x00010000
    PRESSURE = 0x00020000
    MY18B20 = 0x00040000
    IUS = 0x00080000
    PLM = 0x00100000
    BUTTON = 0x00200000
    FINDMY = 0x00400000

# from cmd_parser.h
class CmdId(IntEnum):
    DEVID    = 0x00 # Get dev id, version, services
    DNAME    = 0x01 # Get/Set device name, "\0" - default: THB2_xxxx
    GDEVS    = 0x02 # Get address devices
    I2C_SCAN = 0x03 # I2C scan
    I2C_UTR  = 0x04 # Universal I2C/SMBUS read-write
    SEN_ID   = 0x05    # Get sensor ID
    FLASH_ID = 0x06    # Get Flash JEDEC ID
    SERIAL   = 0x07 # Get serial string
    DEV_MAC  = 0x10 # Get/Set MAC [+RandMAC], [size]<mac[6][randmac[2]]>
    FIX_MAC  = 0x11 # Fixed MAC (не безопасная операция, переписывает сектор 0x1000 Flash)
    BKEY     = 0x18 # Get/Set beacon bindkey in EEP
    COMFORT  = 0x20 # Get/Set comfort parameters
    EXTDATA  = 0x22 # Get/Set show ext. data
    UTC_TIME = 0x23 # Get/Set utc time (if USE_CLOCK = 1)
    TADJUST  = 0x24 # Get/Set adjust time clock delta (in 1/16 us for 1 sec)
    CFS      = 0x25 # Get/Set sensor config
    CFS_DEF  = 0x26 # Get/Set default sensor config
    MEASURE  = 0x33 # Start/stop notify measures in connection mode
    LOGGER   = 0x35 # Read memory measures
    CLRLOG   = 0x36 # Clear memory measures
    RDS      = 0x40 # Get/Set Reed switch config (DIY devices)
    TRG      = 0x44 # Get/Set trigger data config
    TRG_OUT  = 0x45 # Get/Set trg out, Send Reed switch and trg data
    HXC      = 0x49 # Get/Set HX71X config
    CFG      = 0x55    # Get/Set device config
    CFG_DEF  = 0x56    # Set default device config
    LCD_DUMP = 0x60 # Get/Set lcd buf
    LCD_FLG  = 0x61 # Start/Stop notify lcd dump and ...
    PINCODE  = 0x70 # Set new PinCode 0..999999
    MTU      = 0x71 # Request Mtu Size Exchange (23..255)
    REBOOT   = 0x72 # Set Reboot on disconnect
    SET_OTA	 = 0x73 # Extension BigOTA: Get/set address and size OTA, erase sectors
    # Debug commands
    DEBUG    = 0xDE  # Send data to LCD

# from config.h
class ConfigFlag(IntFlag):
    MEAS_NOTIFY   = 0x00000001
    SHOW_TIME     = 0x00000002
    SHOW_SMILEY   = 0x00000004
    SHOW_TRG      = 0x00000008
    DISPLAY_OFF   = 0x00000010
    ADV_CRYPT     = 0x00000020
    SHOW_TF       = 0x00000040
    FINDMY        = 0x00000080
    DISPLAY_SLEEP = 0x00000100

def print_error(text: str):
    print(f"\033[0;31m{text}\033[0m", file=sys.stderr, flush=True)

def error_exit(text: str, *, exit_code=1):
    print_error(text)
    sys.exit(exit_code)

def _recursive_update(data: dict, update_data: Mapping) -> dict: 
    if update_data:
        for k, v in update_data.items():
            if isinstance(v, Mapping) and (k in data):
                data[k] = _recursive_update(data[k], v)
            else:
                data[k] = v

    return data


# see ble_ota.c
def crc16(data: bytes) -> int:
    poly = (0, 0xa001) # 0x8005 <==> 0xa001
    crc = 0xffff

    for ds in data:
        for _ in range(8):
            crc = (crc >> 1) ^ poly[(crc ^ ds) & 1]
            ds >>= 1
    return crc


class SmileyMode(Enum):
    OFF = "off"
    SHOW_COMFORT = "show_comfort"
    SHOW_TRIGGER = "show_trigger"

class DisplayMode(Enum):
    OFF = "off"
    ALWAYS_ON = "always_on"
    ON_DEMAND = "on_demand" # not implemented yet

class TempUnit(Enum):
    CELSIUS = "celsius"
    FAHRENHEIT = "fahrenheit"


class StrictBaseModel(pydantic.BaseModel):
    model_config = pydantic.ConfigDict(extra='forbid', strict=True, str_to_lower=True)

class NoExtraModel(pydantic.BaseModel):
    model_config = pydantic.ConfigDict(extra="forbid")

class TemperatureComfortSettings(NoExtraModel):
    min: Annotated[float, pydantic.Field(ge=-327.68, le=327.67)]
    max: Annotated[float, pydantic.Field(ge=-327.68, le=327.67)]
    @pydantic.model_validator(mode='after')
    def validate(self) -> Self:
        if self.min > self.max:
            raise ValueError("'min' may not exceed 'max'")
        return self

class HumidityComfortSettings(NoExtraModel):
    min: Annotated[float, pydantic.Field(ge=0.0, le=100.0)]
    max: Annotated[float, pydantic.Field(ge=0.0, le=100.0)]
    @pydantic.model_validator(mode='after')
    def validate(self) -> Self:
        if self.min > self.max:
            raise ValueError("'min' may not exceed 'max'")
        return self

class ComfortSettings(NoExtraModel):
    temperature: TemperatureComfortSettings
    humidity: HumidityComfortSettings

class TemperatureTriggerSettings(NoExtraModel):
    threshold: Annotated[float, pydantic.Field(ge=-327.68, le=327.27)]
    hysteresis: Annotated[float, pydantic.Field(ge=0.0, le=327.27)]

class HumidityTriggerSettings(NoExtraModel):
    threshold: Annotated[float, pydantic.Field(ge=0.0, le=100.0)]
    hysteresis: Annotated[float, pydantic.Field(ge=0.0, le=100.0)]

class TriggerSettings(NoExtraModel):
    temperature: TemperatureTriggerSettings
    humidity: HumidityTriggerSettings

class DisplaySettings(NoExtraModel):
    mode: DisplayMode
    show_time: bool
    temp_unit: TempUnit
    smiley: SmileyMode

class BleAdvertisingSettings(NoExtraModel):
    interval: Annotated[float, pydantic.Field(ge=1*0.0625, le=160*0.0625)]
    encrypted: bool
    bind_key: Annotated[bytes, pydantic.Field(min_length=16, max_length=16)] = None
    
    # parse/serialize bindkey as hex
    model_config = pydantic.ConfigDict(ser_json_bytes='hex', val_json_bytes='hex')

class Settings(NoExtraModel):
    display: DisplaySettings
    measurement_notify: bool
    tx_power: Annotated[int, pydantic.Field(ge=0, le=63)]
    find_my: bool
    ble_advertising: BleAdvertisingSettings
    connection_latency: Annotated[float, pydantic.Field(ge=0.030, le=7.680)]
    meas_interval: Annotated[float, pydantic.Field(ge=0.0)] # maximum determined by ble_advertising.interval
    average_measurements: Annotated[int, pydantic.Field(ge=0, le=255)] # 0 == off
    battery_meas_interval: Annotated[float, pydantic.Field(ge=0, le=255)]
    comfort: ComfortSettings = None
    trigger: TriggerSettings = None

    @property
    def advertising_interval_value(self) -> int:
        """The raw value used to encode the advertising interval, in units of 62.5ms."""
        return round(self.ble_advertising.interval / 0.0625)
    @property
    def meas_interval_value(self) -> int:
        """The raw value used to encode the measurement interval."""
        return max(1, round(self.meas_interval / self.ble_advertising.interval))

    @property
    def connection_latency_value(self) -> int:
        """The raw value used to encode the connection latency for the device."""
        return round(((1000 * self.connection_latency) / 30) - 1)

    @pydantic.model_validator(mode='after')
    def post_validate(self) -> Self:
        advertising_interval_rounded = self.advertising_interval_value * 0.0625 # fix rounding

        max_meas_interval = 255 * advertising_interval_rounded
        if self.meas_interval > max_meas_interval:
            raise ValueError(f'meas_interval too large, maximum value is {max_meas_interval}')
    
        if self.comfort is None and self.trigger is not None:
            raise ValueError('"comfort" key missing, which is implied by "trigger"')

        return self


class InvalidFirmware(ValueError):
    pass

class OtaFirmware:
    OTA_MAX_SIZE = 0x30000
    OTA_MAGIC = b"PHY6"

    def __init__(self, image: bytes):
        # Test the firmware (similar to what "testFwOTA" in the html file does)
        fsize = len(image)
        if fsize < 20:
            raise InvalidFirmware("Improper size of binary firmware")
        if fsize > self.OTA_MAX_SIZE:
            raise InvalidFirmware(f"Firmware is bigger than {self.OTA_MAX_SIZE}")
        if fsize != ((fsize & 0x1ffff0) + 4): # 4 bytes crc32
            raise InvalidFirmware("Inappropriate format of the firmware file size'")

        self.magic = image[:4]
        self.num_segments, self.start_address, self.size = struct.unpack("<III", image[4:16])
        if self.magic != self.OTA_MAGIC:
            raise InvalidFirmware("Unsupported firmware type.")

        if self.num_segments >= 16: # differs from HTML file, but the format only supports 15 segments
            raise InvalidFirmware("Wrong number of segments")
        if (self.size + 4) != fsize:
            raise InvalidFirmware("Wrong size in header")
        # crc32 check

        calculated_crc = 0xffffffff - crc32(image[:self.size])
        expected_crc = int.from_bytes(image[self.size:], 'little', signed=False)
        if calculated_crc != expected_crc:
            raise InvalidFirmware("Checksum error")

        # pad to multiple of 16 (image size is guaranteed to be multiple of 16 + crc32)
        self._block_size = 16
        pad_size = self._block_size - (len(image) % self._block_size)
        self._image = image + (pad_size * b'\xff')
        assert (len(self._image) % self._block_size) == 0

    def __str__(self) -> str:
        return f"<firmware size={len(self._image)}>"

    @property
    def num_blocks(self) -> int:
        return len(self._image) // self._block_size

    def iter_blocks(self) -> Iterator[Buffer]:
        # Each block consists of
        # * 2 bytes block index
        # * data bytes
        # * 2 byte crc
        for blk_idx in range(self.num_blocks):
            offset = blk_idx * self._block_size
            block = self._image[offset:(offset + self._block_size)]
            data_without_crc = struct.pack("<H", blk_idx) + block
            yield data_without_crc + struct.pack("<H", crc16(data_without_crc))

class OtaErrorCode(IntEnum):
    SUCCESS         = 0
    UNKNOWN_CMD     = 1
    NO_START        = 2
    NO_PARAM        = 3
    ERR_PARAM       = 4
    PKT_SIZE_ERR    = 5
    PKT_CRC_ERR     = 6
    PACKET_LOSS     = 7
    WRITE_FLASH_ERR = 8
    OVERFLOW        = 9
    FW_CHECK_ERR    = 10
    FW_CRC32_ERR    = 11
    END             = 255

class OtaError(RuntimeError):
    def __init__(self, msg: int | OtaErrorCode | str):
        if msg in OtaErrorCode:
            msg = OtaErrorCode(msg).name
        super().__init__(f"OTA Error: {msg}")

class UnsupportedCommand(Exception):
    pass


class THBClient:
    def __init__(self, address, *, timeout: float = 60, **kwargs):
        self._bleak_client = BleakClient(address, timeout=timeout, **kwargs)
        self._message_queue = asyncio.Queue()
        self._protocol_version = None
        self._sw_version = None
        self._hw_version = None
        self._features = None

    async def _read_characteristic(self, uuid):
        return await self._bleak_client.read_gatt_char(uuid)

    def _notify_callback(self, sender, data: bytearray) -> None:
        self._message_queue.put_nowait(data)

    @property
    def address(self):
        return self._bleak_client.address

    async def __aenter__(self) -> THBClient:
        await self._bleak_client.connect()

        # read & store device info
        devinfo = await self._read_characteristic(CMD_UUID)
        devinfo_format = "<xBHHHL"
        expected_len = struct.calcsize(devinfo_format)
        if (got_len := len(devinfo)) < expected_len:
            raise ValueError(f"Unexpected data size: Got {got_len}, expected at least {expected_len}")

        self._protocol_version, self._hw_version, self._sw_version, _, self._services = struct.unpack(devinfo_format, devinfo[:expected_len])

        await self._bleak_client.start_notify(CMD_UUID, self._notify_callback)

        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb) -> None:
        await self._bleak_client.disconnect()

    @property
    def protocol_version(self):
        return self._protocol_version
    @property
    def sw_version(self):
        # BCD-coded
        major = self._sw_version >> 4
        minor = self._sw_version & 0xF
        return f"{major}.{minor}"

    @property
    def hw_version(self):
        hw_table = {
            19: "THB2",
            20: "BTH01",
            21: "TH05",
            23: "THB1",
            24: "TH05D",
            25: "TH05F",
            26: "THB3",
            32: "KEY2",
            34: "TH04"
        }
        return hw_table.get(self._hw_version, f"{self._hw_version:04x}")

    @property
    def features(self):
        return [feature for feature in Features if (self._services & feature.value)]
    def has_feature(self, feature: Features) -> bool:
        return self._services & feature.value
    @property
    def has_display(self) -> bool:
        return self.has_feature(Features.SCREEN)

    async def message(self, cmd_filter: int | CmdId | None = None, timeout : float = float('inf')) -> bytearray:
        while True:
            if math.isfinite(timeout):
                msg = await asyncio.wait_for(self._message_queue.get(), timeout)
            else:
                msg = await self._message_queue.get()
            self._message_queue.task_done() # irrelevant for now
            if cmd_filter is None:
                return msg
            if (len(msg) > 0) and (msg[0] == cmd_filter):
                return msg

    async def write_command(self, cmd_id: CmdId, cmd_data: Buffer | None = None) -> None:
        cmd_byte = bytes((cmd_id,))
        await self._bleak_client.write_gatt_char(CMD_UUID, (cmd_byte + cmd_data) if cmd_data else cmd_byte)

    async def command_response(self, cmd_id: CmdId, cmd_data: Buffer | None = None) -> bytearray:
        """Sending a command request and await its response."""
        await self.write_command(cmd_id, cmd_data)
        msg = await self.message(cmd_id)
        if (len(msg)) == 2 and (msg[1] == 0xFF):
            raise UnsupportedCommand()
        return msg[1:]

    @staticmethod
    def _decode_utf8z(data: Buffer) -> str:
        zero_pos = data.find(0)
        return (data if (zero_pos < 0) else data[0:zero_pos]).decode('utf-8')

    async def read_serial(self) -> str:
        return self._decode_utf8z(await self.command_response(CmdId.SERIAL))

    async def read_name(self) -> str:
        return self._decode_utf8z(await self.command_response(CmdId.DNAME))

    async def restore_default_name(self) -> str:
        return self._decode_utf8z(await self.command_response(CmdId.DNAME, b'\0'))

    async def write_name(self, new_name: str) -> str:
        return self._decode_utf8z(await self.command_response(CmdId.DNAME, new_name.encode('utf-8') + b'\0'))

    async def read_sensor_id(self):
        response = await self.command_response(CmdId.SEN_ID)
        if len(response) >= 6:
            mid, vid, i2c, sens_type = struct.unpack('<HHBB', response)
            # see TH_SENSOR_... in sensors.h
            sens_type = {
                0: 'NONE',
                1: 'SHTC3',
                2: 'SHT4x',
                3: 'SHT30',
                4: 'CHT8305',
                5: 'AHT2x',
                6: 'CHT8215'
            }.get(sens_type, "<unknown>")

        elif len(response) == 5:
            # currently buggy - sensor type missing
            mid, vid, i2c = struct.unpack('<HHB', response)
            sens_type = "<unknown>"
        else:
            raise RuntimeError("Cannot decode sensor information")

        return {'type': sens_type, 'mid': mid, 'vid': vid, 'i2c_address': i2c}

    async def read_flash_info(self) -> dict[str, Any]:
        flash_id, capacity = struct.unpack("<LL", await self.command_response(CmdId.FLASH_ID))
        return {'id': flash_id, 'capacity': capacity}

    async def read_temperature_service(self) -> float | None:
        try:
            return int.from_bytes(await self._read_characteristic(TEMP_UUID), 'little') / 100.0
        except BleakCharacteristicNotFoundError:
            return  None

    async def read_humidity_service(self) -> float | None:
        try:
            return int.from_bytes(await self._read_characteristic(HUMID_UUID), 'little') / 100.0
        except BleakCharacteristicNotFoundError:
            return None

    async def read_battery_service(self) -> int | None:
        try:
            return int.from_bytes(await self._read_characteristic(BAT_UUID)) # single byte
        except BleakCharacteristicNotFoundError:
            return None

    async def cmd_time(self, set_time: datetime | None = None) -> datetime:
        if set_time is None:
            response = await self.command_response(CmdId.UTC_TIME)
        else:
            set_time_utc = int(set_time.astimezone(timezone.utc).timestamp())
            response = await self.command_response(CmdId.UTC_TIME, struct.pack("<L", set_time_utc))

        if len(response) != 4:
            raise RuntimeError("Failed to read time")

        utc_device = int.from_bytes(response, 'little', signed=False)
        return datetime.fromtimestamp(utc_device, timezone.utc).astimezone()

    async def _read_settings_data(self) -> tuple[Buffer, Buffer, Buffer]:
        config_data = await self.command_response(CmdId.CFG)
        trigger_data = await self.command_response(CmdId.TRG)
        bk_data = await self.command_response(CmdId.BKEY)
        return config_data, trigger_data, bk_data

    @staticmethod
    def _decode_settings(config_data: Buffer, trg_data: Buffer, bk_data: Buffer) -> Settings:
        (
            flags,
            tx_power,
            advertising_interval_value,
            connect_latency_value,
            measure_interval_value,
            battery_meas_interval,
            averaging_measurements,
        ) = struct.unpack("<LBBBxBBBx", config_data)
        flags = ConfigFlag(flags)

        show_smiley = ConfigFlag.SHOW_SMILEY in flags
        smiley_shows_trigger = ConfigFlag.SHOW_TRG in flags
        display_sleep = ConfigFlag.DISPLAY_SLEEP in flags
        display_settings = DisplaySettings(
            mode=DisplayMode.OFF if (ConfigFlag.DISPLAY_OFF in flags) else (DisplayMode.ON_DEMAND if display_sleep else DisplayMode.ALWAYS_ON),
            temp_unit=TempUnit.FAHRENHEIT if (ConfigFlag.SHOW_TF in flags) else TempUnit.CELSIUS,
            show_time=ConfigFlag.SHOW_TIME in flags,
            smiley=SmileyMode.OFF if not show_smiley else (SmileyMode.SHOW_TRIGGER if smiley_shows_trigger else SmileyMode.SHOW_COMFORT)
        )
        find_my = ConfigFlag.FINDMY in flags

        adv_settings = BleAdvertisingSettings(
            interval=0.0625 * advertising_interval_value,
            encrypted=ConfigFlag.ADV_CRYPT in flags,
            bind_key=bk_data if (len(bk_data) == 16) else None
        )

        comfort_setting = None
        if len(trg_data) >= 8:
            temp_min, temp_max, humid_min, humid_max = struct.unpack("<hhhh", trg_data[:8])
            comfort_setting = ComfortSettings(
                temperature=TemperatureComfortSettings(min=temp_min * 0.01, max=temp_max * 0.01),
                humidity=HumidityComfortSettings(min=humid_min * 0.01, max=humid_max * 0.01)
            )

        trigger_settings = None
        if len(trg_data) >= 16:
            temp_thres, humid_thres, temp_hyst, humid_hyst = struct.unpack("<hhhh", trg_data[8:16])
            trigger_settings = TriggerSettings(
                temperature = TemperatureTriggerSettings(threshold=temp_thres * 0.01, hysteresis=temp_hyst * 0.01),
                humidity = HumidityTriggerSettings(threshold=humid_thres * 0.01, hysteresis=humid_hyst *  0.01)
            )

        return Settings(
            display=display_settings,
            measurement_notify=ConfigFlag.MEAS_NOTIFY in flags,
            tx_power=tx_power,
            find_my=find_my,
            ble_advertising=adv_settings,
            connection_latency=0.001 * ((connect_latency_value + 1) * 30),
            meas_interval=measure_interval_value * adv_settings.interval,
            battery_meas_interval=battery_meas_interval,
            average_measurements=averaging_measurements,
            comfort=comfort_setting,
            trigger=trigger_settings,
        )

    async def read_settings(self) -> Settings:
        return self._decode_settings(*(await self._read_settings_data()))

    async def write_settings(self, new_settings: Settings) -> Settings:
        config_data, trigger_data, bk_data = await self._read_settings_data()

        if new_settings is not None:
            flags = ConfigFlag(0)
            if new_settings.measurement_notify:
                flags |= ConfigFlag.MEAS_NOTIFY
            if new_settings.display.show_time:
                flags |= ConfigFlag.SHOW_TIME
            if new_settings.display.mode == DisplayMode.OFF:
                flags |= ConfigFlag.DISPLAY_OFF
            if new_settings.display.mode == DisplayMode.ON_DEMAND:
                flags |= ConfigFlag.DISPLAY_SLEEP
            if new_settings.display.smiley != SmileyMode.OFF:
                flags |= ConfigFlag.SHOW_SMILEY
            if new_settings.display.smiley == SmileyMode.SHOW_TRIGGER:
                flags |= ConfigFlag.SHOW_TRG
            if new_settings.display.temp_unit == TempUnit.FAHRENHEIT:
                flags |= ConfigFlag.SHOW_TF
            if new_settings.ble_advertising.encrypted:
                flags |= ConfigFlag.ADV_CRYPT
            if new_settings.find_my:
                flags |= ConfigFlag.FINDMY

            new_config_data = struct.pack(
                "<LBBBxBBBx",
                flags,
                new_settings.tx_power,
                new_settings.advertising_interval_value,
                new_settings.connection_latency_value,
                new_settings.meas_interval_value,
                round(new_settings.battery_meas_interval),
                new_settings.average_measurements,
            )

            new_trg_data = bytearray(trigger_data)
            if (len(new_trg_data) >= 8) and (comfort := new_settings.comfort) is not None:
                new_trg_data[:8] = struct.pack("<hhhh",
                    round(100 * comfort.temperature.min),
                    round(100 * comfort.temperature.max),
                    round(100 * comfort.humidity.min),
                    round(100 * comfort.humidity.max)
                )
                if (len(new_trg_data) >= 16) and (trigger := new_settings.trigger) is not None:
                    new_trg_data[8:16] = struct.pack("<hhhh",
                        round(100 * trigger.temperature.threshold),
                        round(100 * trigger.humidity.threshold),
                        round(100 * trigger.temperature.hysteresis),
                        round(100 * trigger.humidity.hysteresis)
                    )

            # Bindkey cannot be cleared once set - prevent attempt to overwrite if missing in settings
            new_bk_data = new_settings.ble_advertising.bind_key or bk_data

            if new_config_data != config_data:
                config_data = await self.command_response(CmdId.CFG, new_config_data)
            else:
                print("Skip updating config settings - unchanged.")
            if new_trg_data != trigger_data:
                trigger_data = await self.command_response(CmdId.TRG, new_trg_data)
            else:
                print("Skip updating comfort/trigger settings - unchanged.")
            if new_bk_data != bk_data:
                bk_data = await self.command_response(CmdId.BKEY, new_bk_data)
            else:
                print("Skip updating Bindkey - unchanged.")

        return self._decode_settings(config_data, trigger_data, bk_data)

    async def restore_default_config(self) -> None:
        """Restore default config."""
        await self.write_command(CmdId.CFG_DEF)
        # There are no default comfort/trigger settings

    @dataclass
    class HistoryRecord:
        index: int
        time: datetime
        temperature: float
        humidity: float
        battery_voltage: float

    async def read_history(self, count: int = 0xFFFF, *, start: int = 0):
        if not self.has_feature(Features.HISTORY):
            raise UnsupportedCommand()

        await self.write_command(CmdId.LOGGER, struct.pack("<HH", count, start))

        while True:
            try:
                data = await self.message(CmdId.LOGGER, timeout=0.5)
            except TimeoutError as e:
                if count == 0:
                    break
                raise e

            if len(data) < 13:
                break # exit early (less than the requested amount available)
            if count == 0:
                break # misbehaving sensor

            index, ts_utc, temp, humid, vbat = struct.unpack("<HLhHH", data[1:])

            yield THBClient.HistoryRecord(
                index=index,
                time=datetime.fromtimestamp(ts_utc, timezone.utc),
                temperature=0.01 * temp,
                humidity=0.01 * humid,
                battery_voltage=0.001 * vbat,
            )
            count -= 1

    async def clear_history(self):
        if not self.has_feature(Features.HISTORY):
            raise UnsupportedCommand()
        magic = b"\x12\x34"
        await self.write_command(CmdId.CLRLOG, magic)


    async def schedule_reboot(self, reboot_param: int = 0x01):
        await self.command_response(CmdId.REBOOT, bytes((reboot_param,)))

    async def cancel_reboot(self):
        await self.schedule_reboot(0)

    async def is_reboot_scheduled(self):
        return await self.command_response(CmdId.REBOOT) != 0

    async def _write_ota_packet(self, data: Buffer) -> None:
        await self._bleak_client.write_gatt_char(OTA_UUID, data)

    @dataclass
    class OtaStatus:
        # See ble_ota.h -> ota_par_t
        err_flag: OtaErrorCode
        version: int
        start_flag: int
        debug_flag: int
        program_offset: int
        pkt_index: int
        pkt_total: int
        fw_value: int
        crc32: int

    async def _get_ota_status(self) -> OtaStatus:
        return self.OtaStatus(*struct.unpack("<BBBBIHHII", await self._read_characteristic(OTA_UUID)))

    async def _verify_ota_status(self) -> OtaStatus:
        status = await self._get_ota_status()
        if status.err_flag != OtaErrorCode.SUCCESS:
            raise OtaError(status.err_flag)
        return status

    async def do_ota(self, firmware: OtaFirmware, progress_notifier: Callable[[float | str], None] = lambda _: None) -> None:
        if Features.OTA not in self.features:
            raise OtaError("Not supported by device")

        # send start sequence
        progress_notifier("Starting OTA upgrade")
        await self._write_ota_packet(struct.pack("<H", 0xFF00))
        await self._write_ota_packet(struct.pack("<H", 0xFF01))

        status = await self._verify_ota_status()
        # Packet index is initialized as UINT16_MAX (such that adding 1 starts at 0)
        if (status.start_flag == 0) or (status.pkt_index != 0xFFFF):
            raise OtaError("Start sequence failed")

        # Now send the packets
        progress_notifier("Transmitting firmware")
        num_packets = 0
        total_packets = firmware.num_blocks
        for idx, block in enumerate(firmware.iter_blocks()):
            if (idx > 0) and ((idx % 10) == 0):
                status = await self._verify_ota_status()
                if status.pkt_index != (idx - 1): # pkt_index always corresponds to prev. packet
                    print(status)
                    raise OtaError("Packet index out of sync, probable packet loss.")

            await self._write_ota_packet(block)
            num_packets += 1
            progress_notifier(100 * num_packets / total_packets) # update percentage

        status = await self._get_ota_status()
        if (err := status.err_flag) != OtaErrorCode.END:
            raise OtaError("Device does not acknowledge end of transfer" if (err == OtaErrorCode.SUCCESS) else err)

        # Note: the pkt_index is not updated for the final packet
        if (status.pkt_total != num_packets) or (status.pkt_index < (num_packets - 2)):
            raise OtaError("Too few packets acknowledged, probable packet loss.")

        progress_notifier("Rebooting into new firmware")
        # This will trigger a soft reset
        await self._write_ota_packet(struct.pack("<H", 0xFF02))

class CsvWriter:
    def __init__(self, file_name: os.PathLike, delimiter = '\t'):
        self._file_name = file_name
        self._delimiter = delimiter

    def __enter__(self) -> Self:
        self._columns = {}
        self._file = open(self._file_name, "w", encoding="utf-8")
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self._file.close()

    def _print(self, *args, **kwargs):
        print(*args, file=self._file, **kwargs)

    def record(self, time, **kwargs):
        assert self._file is not None
        if not self._columns:
            # First call determines list of fields
            self._columns = kwargs.keys()
            self._print("time" + self._delimiter + self._delimiter.join(self._columns))
        
        self._print(f"{time:%Y-%m-%d %H:%M:%S}{self._delimiter}{self._delimiter.join(str(v) for k, v in kwargs.items() if k in self._columns)}")


## Command line Interface #####################################################

def validate_bluetooth_address(ctx, param, value, *, regex=re.compile(r"([0-9a-fA-F]{1,2}:){5}[0-9a-fA-F]{1,2}")):
    if not regex.fullmatch(value):
        raise click.BadParameter(f"'{value}' is not a valid Bluetooth address. Use '01:23:45:67:89:AB' format.")

    return value

def pass_client(func = None, *, connect: bool = False):
    """A decorator that includes the common boilerplate to connect to a THB device."""
    @click.pass_obj
    @functools.wraps(func) # Can this be simplified?
    def wrapper(obj, *args, **kwargs):
        async def stub():
            try:
                client = THBClient(obj.address)
                if connect:
                    async with client:
                        await func(client, *args, **kwargs)
                else:
                    await func(client, *args, **kwargs)
            except BleakError as e:
                error_exit(str(e))
            except UnsupportedCommand:
                error_exit("Command not supported by device or not supported in current mode.")
            except Exception as e:
                print_error(e)
                raise e
        asyncio.run(stub())
    return wrapper

connect_client = functools.partial(pass_client, connect=True)

@click.group(invoke_without_command=True)
@click.option(
    '-a',
    '--address',
    required=True,
    help="Bluetooth device address in \"38:1F:8D:C2:4C:AA\" format",
    metavar="BT_ADDR",
    callback=validate_bluetooth_address,
)
@click.pass_context
def cli(ctx, **kwargs):
    ctx.obj = SimpleNamespace(**kwargs)
    # show info by default
    if ctx.invoked_subcommand is None:
        ctx.invoke(info)

@cli.command()
@connect_client
async def info(client):
    """Show device info"""
    print(f"Protocol Version: {client.protocol_version}")
    print(f"Hardware Version: {client.hw_version}")
    print(f"Firmware Version: {client.sw_version}")
    print(f"Features:         {', '.join(f.name for f in client.features)}")
    print(f"Device name:      {await client.read_name()}")
    print(f"Serial number:    {await client.read_serial()}")
    print(f"Flash memory:     {await client.read_flash_info()}")

    print(f"Time:             {await client.cmd_time()}")

    # temperature & humidity
    if client.has_feature(Features.THS):
        print(f"Sensor ID:        {await client.read_sensor_id()}")
        print(f"Temperature:      {await client.read_temperature_service():0.2f} °C")
        print(f"Rel. Humidity:    {await client.read_humidity_service():0.2f} %")

    print(f"Battery level:    {await client.read_battery_service()} %")


@cli.command()
@click.option('--csv', type=click.Path(dir_okay=False, writable=True), required=False, help="Log measurements to CSV file")
@connect_client
async def watch(client: THBClient, csv: os.PathLike | None):
    """Watch measurements send as notifications."""
    if not (await client.read_settings()).measurement_notify:
        error_exit("The device is not configured to send measurement notifications")

    print(f"Receiving measurement notifications from {await client.read_name()} ({client.address})")
    
    with (nullcontext(None) if csv is None else CsvWriter(csv))  as writer:
        while True:
            if len(data := await client.message(CmdId.MEASURE)) >= 11:
                meas_format = "<HhhHBB" # 10 bytes
                count, temp, humi, battery_mv, battery_percent, flags = struct.unpack(meas_format, data[1:11])
                comfort = '😀' if flags & 0x04 else '😡'
                
                temp_degree = 0.01 * temp
                humid_percent = 0.01 * humi
                battery_v = 0.001 * battery_mv
                meas_string = f"{comfort} Measurement {count}: 🌡 {temp_degree:.2f}°C, 💧 {humid_percent:.2f}%, 🔋 {battery_percent}% ({battery_v:.1f}V)"

                record = {'temp_celsius': temp_degree, 'humid_percent': humid_percent, 'battery_v': battery_v, 'battery_percent': battery_percent}

                if len(data) >= 15:
                    time = datetime.fromtimestamp(int.from_bytes(data[11:15], 'little', signed=False), timezone.utc)
                    meas_string += f", 🕑 {time.astimezone():%c}"
                else:
                    time = datetime.fromtimestamp(0, timezone.utc) # fallback for CsvWriter

                if len(data) >= 19:
                    impulse_count = int.from_bytes(data[15:19], 'little', signed=False)
                    meas_string += f", impulse count = {impulse_count}"
                    record['impulse_count'] = impulse_count

                print(meas_string)

                if writer is not None:
                    writer.record(time, **record)

# ========== Commands for History/Logged data ==========
@cli.group(
    help="Read/clear logged history data.",
    invoke_without_command=True
)
@click.pass_context
def history(ctx):
    if ctx.invoked_subcommand is None:
        ctx.invoke(read_history)

@history.command(name="read")
@click.option('--first', type=click.IntRange(1, 0xFFFF), default=1, metavar="NUM", help="First record to retrieve")
@click.option('--last', type=click.IntRange(1, 0xFFFF), default=1000, metavar="NUM", help="How many records to retrieve")
@click.option('--quiet', is_flag=True, help="Do not dump history records to screen (useful when storing data in file)")
@click.option('--csv', type=click.Path(dir_okay=False, writable=True), required=False, help="Write results to CSV")
@click.option('--pandas', 'pandas_file', type=click.Path(dir_okay=False, writable=True), required=False, help="Write results as Pandas dataframe")
@click.option('--graph', is_flag=True, help="Visualize history data (requires matplotlib)")
@pass_client
async def read_history(client: THBClient, first: int, last: int, quiet: bool, csv: os.PathLike | None, pandas_file: os.PathLike | None, graph: bool):
    """Read history data and optionally save/display it."""

    if first > last:
        raise click.BadArgumentUsage(f"Value of --first ({first}) not exceed --last ({last})")

    # Locally import big packages optionally needed below
    if graph:
        try:
            from matplotlib import pyplot as plt
        except ImportError:
            error_exit("matplotlib not installed")

    if pandas_file is not None:
        try:
            import pandas as pd
        except ImportError:
            error_exit("Pandas not installed")

    # Rad history data
    records = []

    async with client:
        expect_next = first

        async for record in client.read_history(last - first + 1, start=first - 1):
            if record.index < expect_next:
                print_error("Received history entry out of order")
            else:
                if record.index > expect_next:
                    print_error("Gap in history data.")
                expect_next = record.index + 1

            records.append(record)

            if not quiet:
                print(f"Entry {record.index:>5}: 🌡 {record.temperature:5.2f}°C 💧 {record.humidity:5.2f}% 🔋 {record.battery_voltage:.1f}V 🕑 {record.time.astimezone():%c}")

        if (num_records := len(records)) > 0:
            print(f"Read {num_records} history entries from {records[-1].time.astimezone():%c} - {records[0].time.astimezone():%c}")
        else:
            print("No history data.")

        if graph:
            client_name = await client.read_name() # name shown in graph title

    if len(records) == 0:
        return

    # reverse order to store/show data from old to new
    records = list(r for r in reversed(records))

    if csv is not None:
        with CsvWriter(csv) as writer:
            for record in records:
                writer.record(time=record.time, temp_celsius=record.temperature, humid_percent=record.humidity, bat_voltage=record.battery_voltage)

    if pandas_file is not None:
        # Save history data as pandas dataframe in pickle file
        df = pd.DataFrame(
            records,
            index=[rec.index for rec in records],
            columns=(
                f for f in THBClient.HistoryRecord.__dataclass_fields__ if f != "index"
            ),
        ).rename(
            columns={ # use same column names as in CSV
                "temperature": "temp_celsius",
                "humidity": "humid_percent",
                "battery_voltage": "bat_voltage",
            }
        )
        df.to_pickle(pandas_file)

    if graph:
        # Show history data with matplotlib
        fig, (axv, axt) = plt.subplots(nrows=2, ncols=1, sharex=True, height_ratios=(1, 4))
        fig.canvas.manager.set_window_title(Path(__file__).stem)
        fig.suptitle(f"History of {client_name} ({client.address})")

        axh = axt.twinx()

        times = [r.time for r in records]
        axt.plot(times, [r.temperature for r in records], 'r-')
        axt.grid(True)
        axt.set_ylabel('Temperature [°C]', color='r')
        axt.tick_params(axis='y', colors='r')
        axt.set_xlabel('Time')
        
        axh.plot(times, [r.humidity for r in records], 'b-')
        axh.set_ylabel('Humidity [%]', color='b')
        axh.tick_params(axis='y', colors='b')

        axv.plot(times, [r.battery_voltage for r in records], 'k-')
        axv.set_ylabel('Battery [V]')
        axv.grid(True)

        plt.show()


@history.command(name="clear")
@connect_client
async def clear_history(client):
    """Clear measurement history."""
    await client.clear_history()

# ========== Commands for device config ==========
@cli.group(
    help="Show or manipulate device settings.",
    invoke_without_command=True
)
@click.pass_context
def config(ctx):
    if ctx.invoked_subcommand is None:
        ctx.invoke(show_settings)

@config.command(name="show")
@connect_client
async def show_settings(client):
    """Read and show device settings."""
    name, settings = await client.read_name(), await client.read_settings()

    headline = f"Config of {client.address} ({name})"
    print(headline)
    print("-" * len(headline))
    # round-trip via json to avoid RepresenterErrors (e.g., for enums)
    yaml.safe_dump(yaml.safe_load(settings.model_dump_json()), sys.stdout, indent=4)


def _save_settings(file, settings: Settings, *, client_address, client_name) -> None:
    settings_json = settings.model_dump_json(exclude_none=True, indent=4)
    if file.name.endswith('yaml') or file.name.endswith('yml'):
        print(f"# Settings from {client_address} ({client_name}), saved at {datetime.now().strftime('%D %T')}", file=file)
        # round-trip via json to avoid RepresenterErrors (e.g., for enums)
        yaml.safe_dump(yaml.safe_load(settings_json), file, indent=4)
    else:
        file.write(settings_json)


@config.command(name="save")
@click.argument("file", metavar="<file>", type=click.File(mode='w', lazy=True, encoding='utf-8'))
@connect_client
async def save_settings(client, file):
    """Save settings to YAML or Json file."""
    _save_settings(
        file,
        await client.read_settings(),
        client_address=client.address,
        client_name=await client.read_name(),
    )


@config.command(name="restore")
@click.argument("file", metavar="<file>", type=click.File(mode='r', encoding='utf-8'))
@click.option("-u", "--update", is_flag=True, help="Update file with settings read back from device")
@pass_client
async def restore_settings(client, file, update: bool):
    """Restore settings from <file> (in json or yaml format)."""
    if update and not os.access(file.name, os.W_OK):
        raise click.UsageError("'--update' requested, but file is not writable.")

    update_data = yaml.safe_load(file)

    async with client:
        # allow partial updates by recursively merging update_data into current settings
        raw_settings = _recursive_update((await client.read_settings()).model_dump(), update_data)

        try:
            settings = Settings.model_validate(raw_settings)
        except pydantic.ValidationError as e:
            error_exit(e)

        settings = await client.write_settings(settings)

        if update:
            file.close()
            with open(file.name, 'w') as f:
                _save_settings(
                    f,
                    settings,
                    client_address=client.address,
                    client_name=await client.read_name(),
                )


@config.command(name="set-time")
@connect_client
async def set_time(client):
    """Set device time from computer."""
    print(f"Device time is now {await client.cmd_time(datetime.now())}")

@config.command(name="set-name")
@click.argument("new_name", metavar="NAME", type=str, required=True)
@pass_client
async def set_name(client, new_name):
    """Set device time from computer."""
    if not new_name or (encoded_len := len(new_name.encode('utf-8'))) > 20:
        raise click.BadParameter(f"Name may have between 1 and 20 bytes, but '{new_name}' requires {encoded_len} bytes.")

    async with client:
        print(f"Device name changed to '{await client.write_name(new_name)}'")


@config.command(name="time-adjust")
@connect_client
async def time_adjust(client):
    # not supported - but test that it is not
    result = await client.command_response(CmdId.TADJUST)
    print(result)

@config.command(name="reset")
@connect_client
async def reset_config(client):
    """Restore default settings"""
    await client.restore_default_config()
    print(f"Default configuration restored.")
    name = await client.restore_default_name()
    print(f"Device name reverted to '{name}'.")
    # Note: Cannot reset comfort/trigger settings -> There is no command for it.


def validate_reboot_arg(ctx, param, value):
    if isinstance(value, str):
        value = value.lower()
        if value == "ota":
            return REBOOT_CODE_OTA
        try:
            if value.startswith("0x"):
                value = int(value[2:], 16)
            else:
                value = int(value)
        except ValueError:
            raise click.BadParameter(f"Reboot parameter must be a (hex) number or the value 'ota'")
    
    if value < 0 or value > 255:
        raise click.BadParameter(f"Reboot parameter must be a value between 0 and 255 (1 byte)")

    return value

@cli.command()
@click.argument("reboot_param" , metavar="PARAM", type=str, default=0x01, callback=validate_reboot_arg)
@connect_client
async def reboot(client, reboot_param):
    """Send reboot request.
    
    PARAM: Optional parameter forwarded to the boot routine.

    Used "ota" (or 0x33) to reboot into the bootloader for OTA update.
    """
    await client.schedule_reboot(reboot_param)
    if await client.is_reboot_scheduled():
        print("Will reboot after disconnection")
    else:
        error_exit("Failed to schedule reboot")

@cli.command()
@click.argument("file", metavar="<file>", type=click.Path(dir_okay=False, exists=True))
@pass_client
async def ota_update(client, file):
    """Perform over-the-air update"""
    from tqdm import tqdm # local import, not needed in any other command for now

    ota_data = Path(file).read_bytes()
    try:
        firmware = OtaFirmware(ota_data)
    except InvalidFirmware as e:
        error_exit(str(e))

    print(f"Firmware: {firmware.magic.decode('ascii')}, size = {firmware.size} ({firmware.num_segments} segments)")

    ota_reboot_done = False
    while True:
        print("Connecting...", flush=True)
        async with client:
            if not Features.OTA in client.features:
                if ota_reboot_done:
                    error_exit("OTA feature not supported")

                print("Reboot device into OTA mode...")
                await client.schedule_reboot(REBOOT_CODE_OTA)
                ota_reboot_done = True
                print("IMPORTANT: Reconnecting after reboot might fail due to aggressive GATT caching in BlueZ.")
                print("If you encounter any issues, try setting 'Cache = yes' in '/etc/bluetooth/main.conf' under '[GATT]'")
                continue
            
            # Perform the actual OTA update with progress indicator
            try:
                with tqdm(total=100, colour='blue', desc="Writing firmware", bar_format='{percentage:3.0f}% |{bar}| {elapsed}<{remaining}') as pbar:
                    def update_progress(progress: str | float) -> None:
                        if isinstance(progress, str):
                            pbar.write(progress)
                        else:
                            pbar.update(progress - pbar.n)

                    await client.do_ota(firmware, progress_notifier=update_progress)
            except OtaError as e:
                error_exit(str(e))

            break


if __name__ == "__main__":
    if sys.hexversion < 0x030c0000:
        error_exit("Python 3.10+ required")
    cli()
