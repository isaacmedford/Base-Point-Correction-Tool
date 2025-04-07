import warnings
warnings.filterwarnings("ignore", category=DeprecationWarning)

import sys
import os
import csv
import glob
import pyproj
import pandas as pd
import numpy as np
import logging
import shutil
from datetime import datetime, timedelta
import georinex as gr
import matplotlib
matplotlib.use('Qt5Agg')
from matplotlib.figure import Figure
from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas
from matplotlib.backends.backend_qt5agg import NavigationToolbar2QT as NavigationToolbar
from PyQt5.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout,
                           QHBoxLayout, QPushButton, QLabel, QLineEdit,
                           QFileDialog, QGroupBox, QComboBox,
                           QMessageBox, QFrame, QDoubleSpinBox, QGridLayout,
                           QTextBrowser, QSplitter, QSizePolicy, QDialog, QTreeWidget, QTreeWidgetItem,
                           QSpacerItem)
from PyQt5.QtCore import Qt, QSize, QThread, pyqtSignal, QRectF, QPointF, QTimer
from PyQt5.QtGui import QFont, QPalette, QColor, QPainter, QPen, QBrush, QPainterPath
import PyQt5.sip
import json
from PIL import Image, ExifTags
import re
import piexif
import subprocess
from piexif import ExifIFD, GPSIFD
import traceback
from math import radians, sin, cos, sqrt, asin

# Set up logging
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler("base_point_correction_debug.log"),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger("Base_Point_Correction")

def gps_week_seconds_to_utc(seconds, year=None):
    """Convert GPS week seconds to UTC datetime.
    
    Args:
        seconds (float): Seconds into the current GPS week
        year (int, optional): Year to use as reference. If None, will determine based on data
        
    Returns:
        datetime: UTC datetime object
    """
    # Calculate week number and seconds within the week
    seconds_in_week = float(seconds)
    
    # If no year provided, try to determine from the seconds value
    # or use the current year as a fallback
    if year is None:
        year = datetime.now().year
    
    # Use a reference date close to data capture time
    # GPS time starts counting from January 6, 1980
    gps_epoch = datetime(1980, 1, 6, 0, 0, 0)
    
    # Find the start of the current GPS week
    # Calculate days since GPS epoch
    days_since_epoch = (datetime(year, 1, 1) - gps_epoch).days
    weeks_since_epoch = days_since_epoch // 7
    
    # Calculate the start of the current GPS week
    week_start = gps_epoch + timedelta(weeks=weeks_since_epoch)
    
    # Adjust to the most recent Sunday before the data
    while week_start.weekday() != 6:  # 6 is Sunday
        week_start += timedelta(days=1)
    
    # Calculate the target date by adding seconds into the week
    target_date = week_start + timedelta(seconds=seconds_in_week)
    
    # Account for leap seconds (as of 2023, there are 18 leap seconds)
    # Note: This is a simplified approach. For precise applications,
    # a more sophisticated leap second handling would be needed
    target_date = target_date - timedelta(seconds=18)
    
    return target_date

def analyze_mission_rpt(rpt_file_path):
    """Analyze mission timing from RPT file.
    
    Args:
        rpt_file_path (str): Path to the RPT file
        
    Returns:
        dict: Dictionary with mission timing information or None if error
    """
    try:
        logger.debug(f"Analyzing mission RPT file: {rpt_file_path}")
        with open(rpt_file_path, 'r') as file:
            data = json.load(file)
        
        root = data["SURVEYING_REPORT_ROOT"]
        basic_info = root["BASIC_INFO_UNIT"]
        cam_info = root["VISIBLE_CAM_INFO_UNIT"]
        
        mission_start_time = basic_info["MISSION_START_TIME"]
        fly_time = basic_info["FLY_TIME"]
        mission_end_time = mission_start_time + fly_time
        
        rtk_info = cam_info["RTK_DETAIL_INFO"]
        first_timestamp = rtk_info[0]["TIME_STAMP"]
        last_timestamp = rtk_info[-1]["TIME_STAMP"]
        
        data_collection_duration = last_timestamp - first_timestamp
        pre_collection_time = first_timestamp - mission_start_time
        post_collection_time = mission_end_time - last_timestamp
        
        # Convert timestamps to readable format
        start_datetime = datetime.fromtimestamp(mission_start_time)
        end_datetime = datetime.fromtimestamp(mission_end_time)
        first_data_datetime = datetime.fromtimestamp(first_timestamp)
        last_data_datetime = datetime.fromtimestamp(last_timestamp)
        
        return {
            "mission_start_time": mission_start_time,
            "mission_start_datetime": start_datetime,
            "mission_end_time": mission_end_time,
            "mission_end_datetime": end_datetime,
            "fly_time_seconds": fly_time,
            "first_data_time": first_timestamp,
            "first_data_datetime": first_data_datetime,
            "last_data_time": last_timestamp,
            "last_data_datetime": last_data_datetime,
            "data_collection_duration": data_collection_duration,
            "pre_collection_time": pre_collection_time,
            "post_collection_time": post_collection_time,
            "total_images": cam_info["TOTAL_CAP_NUM"]
        }
    except Exception as e:
        logger.error(f"Error analyzing RPT file {rpt_file_path}: {str(e)}")
        logger.error(traceback.format_exc())
        return None

class RinexLoadWorker(QThread):
    """Worker thread for loading RINEX data."""
    # Define signals at class level
    progress = pyqtSignal(str)
    error = pyqtSignal(str)
    finished = pyqtSignal(dict)

    def __init__(self, rinex_file, base_lat, base_lon, base_ellh, antenna_height, 
                 antenna_height_units='ft', coord_system_units='ft', parent=None):
        super().__init__(parent)
        self.rinex_file = rinex_file
        self.base_lat = base_lat
        self.base_lon = base_lon
        self.base_ellh = base_ellh
        self.antenna_height = antenna_height
        self.antenna_height_units = antenna_height_units
        self.coord_system_units = coord_system_units

    def extract_time_from_rinex(self):
        """Extract time and satellite information from RINEX file using file reading."""
        try:
            self.progress.emit("Reading RINEX header...")
            
            # Store satellite counts
            satellite_counts = {
                'GPS': 0,
                'GLONASS': 0,
                'Galileo': 0,
                'BeiDou': 0,
                'QZSS': 0
            }
            satellite_total = 0
            
            with open(self.rinex_file, 'r') as f:
                header_lines = []
                for i, line in enumerate(f):
                    header_lines.append(line)
                    if "END OF HEADER" in line:
                        break
                    if i > 100:  # Safety limit for header
                        break
                    
                    # Check for satellite system types in header
                    if "SYS / # / OBS TYPES" in line:
                        system_code = line[0].strip()
                        if system_code == 'G':
                            satellite_counts['GPS'] += 1
                            satellite_total += 1
                        elif system_code == 'R':
                            satellite_counts['GLONASS'] += 1
                            satellite_total += 1
                        elif system_code == 'E':
                            satellite_counts['Galileo'] += 1
                            satellite_total += 1
                        elif system_code == 'C':
                            satellite_counts['BeiDou'] += 1
                            satellite_total += 1
                        elif system_code == 'J':
                            satellite_counts['QZSS'] += 1
                            satellite_total += 1
            
            # Look for time of first observation
            first_obs_time = None
            last_obs_time = None
            
            for line in header_lines:
                if "TIME OF FIRST OBS" in line:
                    # Parse the time information
                    time_parts = line.split()[0:6]  # Get year, month, day, hour, min, sec
                    try:
                        year = int(time_parts[0])
                        month = int(time_parts[1])
                        day = int(time_parts[2])
                        hour = int(time_parts[3])
                        minute = int(time_parts[4])
                        second = float(time_parts[5])
                        
                        first_obs_time = datetime(year, month, day, hour, minute, int(second),
                                                microsecond=int((second % 1) * 1e6))
                        logger.info(f"Found first observation time: {first_obs_time}")
                    except (ValueError, IndexError) as e:
                        logger.warning(f"Error parsing time components: {str(e)}")
                
                if "TIME OF LAST OBS" in line:
                    # Parse the time information
                    time_parts = line.split()[0:6]  # Get year, month, day, hour, min, sec
                    try:
                        year = int(time_parts[0])
                        month = int(time_parts[1])
                        day = int(time_parts[2])
                        hour = int(time_parts[3])
                        minute = int(time_parts[4])
                        second = float(time_parts[5])
                        
                        last_obs_time = datetime(year, month, day, hour, minute, int(second),
                                                microsecond=int((second % 1) * 1e6))
                        logger.info(f"Found last observation time: {last_obs_time}")
                    except (ValueError, IndexError) as e:
                        logger.warning(f"Error parsing time components: {str(e)}")
            
            if not first_obs_time:
                # Try to get time from filename
                filename = os.path.basename(self.rinex_file)
                # Look for pattern like 20250327164535 in filename
                match = re.search(r'(\d{4})(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})', filename)
                if match:
                    year = int(match.group(1))
                    month = int(match.group(2))
                    day = int(match.group(3))
                    hour = int(match.group(4))
                    minute = int(match.group(5))
                    second = int(match.group(6))
                    first_obs_time = datetime(year, month, day, hour, minute, second)
                    logger.info(f"Using time from filename: {first_obs_time}")
                else:
                    raise ValueError("Could not find time information in header or filename")
            
            # If we have first time but not last time, assume a reasonable duration
            if first_obs_time and not last_obs_time:
                # Check if there's data in the file to determine actual duration
                last_obs_time = first_obs_time + timedelta(hours=24)
                logger.info(f"No explicit last observation time found, assuming 24 hours: {last_obs_time}")
            
            return first_obs_time, last_obs_time, satellite_counts, satellite_total
        except Exception as e:
            logger.error(f"Error reading RINEX header: {str(e)}")
            raise

    def run(self):
        try:
            # Get time information directly from file
            rinex_start, rinex_end, satellite_counts, satellite_total = self.extract_time_from_rinex()
            
            self.progress.emit("Processing RINEX data...")
            
            result = {
                'rinex_start': rinex_start,
                'rinex_end': rinex_end,
                'base_lat': self.base_lat,
                'base_lon': self.base_lon,
                'base_ellh': self.base_ellh,
                'antenna_height': self.antenna_height,
                'antenna_height_units': self.antenna_height_units,
                'coord_system_units': self.coord_system_units,
                'satellite_counts': satellite_counts,
                'satellite_total': satellite_total
            }
            
            self.finished.emit(result)
            
        except Exception as e:
            self.error.emit(f"Error reading RINEX data: {str(e)}")

class FlightProcessor(QThread):
    """Worker thread for processing flight and photo data."""
    # Define signals at class level
    progress = pyqtSignal(str)
    error = pyqtSignal(str)
    finished = pyqtSignal(list)  # Signal emits a list of mission dictionaries

    def __init__(self, directory, rinex_start, rinex_end, parent=None):
        super().__init__(parent)
        self.directory = directory
        self.rinex_start = rinex_start
        self.rinex_end = rinex_end
        
    def run(self):
        try:
            self.progress.emit("Processing flight data...")
            logger.debug(f"Analyzing flight data in directory: {self.directory}")
            
            # Process all mission directories in the project folder
            mission_data = []
            
            # Find all DJI_ directories that might contain flight data
            mission_dirs = []
            
            for item in os.listdir(self.directory):
                item_path = os.path.join(self.directory, item)
                if os.path.isdir(item_path) and item.startswith("DJI_"):
                    mission_dirs.append(item_path)
            
            logger.info(f"Found {len(mission_dirs)} potential mission directories")
            
            # If no missions found, we'll return an empty list
            if not mission_dirs:
                logger.info("No mission directories found - nothing to process")
                self.finished.emit([])
                return
                
            # Process each mission directory to find photo timing
            for mission_dir in mission_dirs:
                try:
                    mission_name = os.path.basename(mission_dir)
                    self.progress.emit(f"Analyzing {mission_name}...")
                    
                    mission_info = {
                        'name': mission_name,
                        'directory': mission_dir
                    }
                    
                    # Look for JPG files with EXIF data
                    jpg_files = []
                    for file in os.listdir(mission_dir):
                        if file.lower().endswith('.jpg') and file.startswith('DJI_'):
                            jpg_files.append(os.path.join(mission_dir, file))
                
                    if jpg_files:
                        jpg_files.sort()
                        logger.info(f"Found {len(jpg_files)} JPG files in {mission_name}")
                        
                        # Get first and last photo times
                        first_photo_time = None
                        last_photo_time = None
                        
                        # Try first photo
                        for photo in jpg_files[:5]:  # Try first 5 photos in case first one fails
                            timestamp = get_utc_exposure_time(photo)
                            if timestamp:
                                first_photo_time = timestamp  # Already a datetime object
                                logger.info(f"First photo time: {first_photo_time}")
                                break
                                
                        # Try last photo (fix the slice to get actual last photos)
                        for photo in jpg_files[-5:]:  # Get the last 5 photos
                            timestamp = get_utc_exposure_time(photo)
                            if timestamp:
                                last_photo_time = timestamp  # Already a datetime object
                                logger.info(f"Last photo time: {last_photo_time}")
                                break
                        
                        if first_photo_time and last_photo_time:
                            mission_info['first_photo_time'] = first_photo_time
                            mission_info['last_photo_time'] = last_photo_time
                            mission_info['first_photo_readable'] = first_photo_time.strftime('%Y-%m-%d %H:%M:%S')
                            mission_info['last_photo_readable'] = last_photo_time.strftime('%Y-%m-%d %H:%M:%S')
                            mission_info['photo_count'] = len(jpg_files)
                            
                            # Calculate duration properly
                            photo_duration = (last_photo_time - first_photo_time).total_seconds()
                            mission_info['photo_duration'] = photo_duration
                            
                            logger.info(f"Mission duration: {photo_duration/60:.1f} minutes ({photo_duration} seconds)")
                            logger.info(f"First photo: {mission_info['first_photo_readable']}")
                            logger.info(f"Last photo: {mission_info['last_photo_readable']}")
                            
                            # Check RINEX coverage
                            if self.rinex_start and self.rinex_end:
                                # Add buffer checks (5 minutes before/after)
                                buffer_before = (first_photo_time - self.rinex_start).total_seconds() / 60
                                buffer_after = (self.rinex_end - last_photo_time).total_seconds() / 60
                                
                                mission_info['rinex_buffer_before'] = buffer_before
                                mission_info['rinex_buffer_after'] = buffer_after
                                
                                # Mission is covered if it has at least 2 minutes buffer on each side
                                mission_info['rinex_coverage'] = buffer_before >= 2 and buffer_after >= 2
                            else:
                                mission_info['rinex_coverage'] = False
                    
                    # Add this mission to our results
                    mission_data.append(mission_info)
                
                except Exception as e:
                    logger.warning(f"Error processing mission directory {mission_dir}: {str(e)}")
                    continue
            
            # Send the processed missions data back to the main thread
            logger.debug(f"Flight processing complete, found {len(mission_data)} missions")
            self.finished.emit(mission_data)
            
        except Exception as e:
            logger.error(f"Error processing flight data: {str(e)}")
            logger.error(traceback.format_exc())
            self.error.emit(f"Error processing flight data: {str(e)}")
            # Return empty list on error
            self.finished.emit([])

def update_rinex_base_position(rinex_file, base_lat, base_lon, base_ellh, antenna_height, antenna_height_units='ft', coordinate_system_units='ft', max_shift_meters=5.0):
    """
    Update RINEX base station position with precise coordinates.
    
    Args:
        rinex_file (str): Path to the RINEX file
        base_lat (float): Base station latitude in decimal degrees
        base_lon (float): Base station longitude in decimal degrees
        base_ellh (float): Base station ellipsoidal height in coordinate system units
        antenna_height (float): Antenna height in antenna_height_units
        antenna_height_units (str): Units of antenna height ('ft' or 'm')
        coordinate_system_units (str): Units of coordinate system ('ft' or 'm')
        max_shift_meters (float): Maximum allowed position shift in meters
    
    Returns:
        tuple: (output_file, total_shift, horizontal_shift, vertical_shift, success)
    """
    try:
        logger.info(f"Updating RINEX base position for: {rinex_file}")
        logger.info(f"Input units - Antenna: {antenna_height_units}, Coordinate System: {coordinate_system_units}")
        
        # Convert heights to meters if in feet
        if coordinate_system_units == 'ft':
            base_ellh_m = base_ellh / 3.28083333333333
            logger.info(f"Converting ellipsoidal height from feet ({base_ellh}) to meters ({base_ellh_m})")
        else:
            base_ellh_m = base_ellh
            
        if antenna_height_units == 'ft':
            antenna_height_m = antenna_height / 3.28083333333333
            logger.info(f"Converting antenna height from feet ({antenna_height}) to meters ({antenna_height_m})")
        else:
            antenna_height_m = antenna_height
        
        # Read RINEX header to get current position
        header = gr.rinexheader(rinex_file)
        
        # Extract current position from header
        current_lat = 0
        current_lon = 0
        current_height = 0
        
        if isinstance(header, dict):
            # Get position from dict header
            current_pos = header.get('position', [0, 0, 0])
            if len(current_pos) >= 3:
                # Try to convert from ECEF to lat/lon/height
                try:
                    transformer = pyproj.Transformer.from_crs('EPSG:4978', 'EPSG:4326', always_xy=True)
                    current_lon, current_lat, current_height = transformer.transform(
                        current_pos[0], current_pos[1], current_pos[2]
                    )
                except Exception as e:
                    logger.warning(f"Error converting ECEF to lat/lon: {str(e)}")
            
            # Try to get lat/lon directly if available
            if abs(current_lat) < 0.001:
                current_lat = header.get('lat', 0)
                current_lon = header.get('lon', 0)
                current_height = header.get('height', 0)
        else:
            # Try to parse position from header string
            pos_match = re.search(r'APPROX POSITION XYZ\s+([-\d.]+)\s+([-\d.]+)\s+([-\d.]+)', str(header))
            if pos_match:
                current_pos = [float(pos_match.group(1)), float(pos_match.group(2)), float(pos_match.group(3))]
                
                # Try to convert ECEF to lat/lon/height
                try:
                    transformer = pyproj.Transformer.from_crs('EPSG:4978', 'EPSG:4326', always_xy=True)
                    current_lon, current_lat, current_height = transformer.transform(
                        current_pos[0], current_pos[1], current_pos[2]
                    )
                except Exception as e:
                    logger.warning(f"Error converting ECEF to lat/lon: {str(e)}")
            else:
                current_pos = [0, 0, 0]
        
        # Verify we have valid coordinates
        if abs(base_lat) < 0.001 or abs(base_lon) < 0.001:
            logger.error("Base coordinates appear to be invalid (near zero)")
            return None, 0, 0, 0, False
        
        # Calculate horizontal shift using haversine, with validation
        if abs(current_lat) > 0.001 and abs(current_lon) > 0.001:
            horizontal_shift = haversine(base_lon, base_lat, current_lon, current_lat)
            logger.info(f"Calculated horizontal shift: {horizontal_shift:.4f}m (current pos: {current_lon:.6f}, {current_lat:.6f})")
        else:
            # If current position is 0,0 or very small, consider it invalid/uninitialized
            logger.warning("Current position appears to be uninitialized or 0,0 - setting reasonable horizontal shift")
            horizontal_shift = 0.1  # Set a small reasonable value
        
        # Calculate vertical shift with validation
        if abs(current_height) > 0.001:
            vertical_shift = abs(base_ellh_m - current_height)
            logger.info(f"Calculated vertical shift: {vertical_shift:.4f}m (current height: {current_height:.4f}m)")
        else:
            # If current height is 0 or very small, consider it invalid/uninitialized
            logger.warning("Current height appears to be uninitialized or 0 - setting reasonable vertical shift")
            vertical_shift = 0.1  # Set a small reasonable value
        
        # Validate shift values (cap at reasonable limits to prevent extreme values)
        if horizontal_shift > 1000000:  # More than 1000 km is likely an error
            logger.warning(f"Extremely large horizontal shift detected ({horizontal_shift}m) - capping to 100m")
            horizontal_shift = 100.0
            
        if vertical_shift > 10000:  # More than 10 km vertically is likely an error
            logger.warning(f"Extremely large vertical shift detected ({vertical_shift}m) - capping to 10m")
            vertical_shift = 10.0
        
        # Calculate total shift
        total_shift = sqrt(horizontal_shift**2 + vertical_shift**2)
        
        # Log shifts in both meters and feet
        logger.info(f"Shifts - Meters: total={total_shift:.4f}, h={horizontal_shift:.4f}, v={vertical_shift:.4f}")
        total_shift_ft = total_shift * 3.28083333333333
        h_shift_ft = horizontal_shift * 3.28083333333333
        v_shift_ft = vertical_shift * 3.28083333333333
        logger.info(f"Shifts - Feet: total={total_shift_ft:.4f}, h={h_shift_ft:.4f}, v={v_shift_ft:.4f}")
        
        if total_shift > max_shift_meters:
            logger.warning(f"Position shift exceeds {max_shift_meters:.1f} meters: {total_shift:.4f}")
        
        # Create output filename
        output_dir = os.path.dirname(rinex_file)
        base_name = os.path.basename(rinex_file)
        output_file = os.path.join(output_dir, f"corrected_{base_name}")
        
        # Calculate the combined position (base + antenna)
        # Add antenna height to ellipsoidal height for the actual antenna phase center
        adjusted_ellh_m = base_ellh_m + antenna_height_m
        
        # Convert lat/lon/ellh to ECEF XYZ
        transformer = pyproj.Transformer.from_crs('EPSG:4326', 'EPSG:4978', always_xy=True)
        new_x, new_y, new_z = transformer.transform(base_lon, base_lat, adjusted_ellh_m)
        
        # Format with exact spacing to match RINEX format
        # Each number should be formatted with 7 digits before decimal, 4 after
        # The antenna delta line should align decimals with the XYZ line
        new_pos_str = f"   {new_x:7.4f} {new_y:8.4f}  {new_z:7.4f}"  # Added an extra space at the start
        new_antenna_delta = "        0.0000        0.0000        0.0000"
        logger.info(f"New ECEF position: {new_pos_str}")
        logger.info("Setting antenna delta values to zero")
        
        # Create a corrected version of the RINEX file
        with open(rinex_file, 'r') as infile, open(output_file, 'w') as outfile:
            for line in infile:
                if "APPROX POSITION XYZ" in line:
                    # Replace the position line with new coordinates, maintaining exact spacing
                    outfile.write(f"{new_pos_str}                  APPROX POSITION XYZ\n")
                elif "ANTENNA: DELTA H/E/N" in line:
                    # Zero out the antenna delta, maintaining exact spacing
                    outfile.write(f"{new_antenna_delta}                  ANTENNA: DELTA H/E/N\n")
                else:
                    # Keep other lines unchanged
                    outfile.write(line)
        
        logger.info(f"Created corrected RINEX file: {output_file}")
        
        return output_file, total_shift, horizontal_shift, vertical_shift, True
        
    except Exception as e:
        logger.error(f"Error updating RINEX base position: {str(e)}")
        logger.error(traceback.format_exc())  # Add stack trace for debugging
        return None, 0, 0, 0, False

class DJIPPKPro(QMainWindow):
    """Main window class for DJI PPK Pro application."""
    # Define signals at class level
    status_updated = pyqtSignal(str)
    progress_updated = pyqtSignal(int)

    def __init__(self):
        super().__init__()
        self.setWindowTitle("Base Point Correction Tool")
        self.base_station_data = {}
        self.rinex_worker = None
        self.flight_processor = None
        self.setup_ui()
        
    def handle_rinex_completion(self, result):
        """Handle completion of RINEX data processing."""
        try:
            if not result:
                raise ValueError("No RINEX data received")
                
            # Extract data from result
            rinex_start = result.get('rinex_start')
            rinex_end = result.get('rinex_end')
            base_lat = result.get('base_lat')
            base_lon = result.get('base_lon')
            base_ellh = result.get('base_ellh')
            antenna_height = result.get('antenna_height')
            antenna_height_units = result.get('antenna_height_units', 'ft')
            coord_system_units = result.get('coord_system_units', 'ft')
            satellite_counts = result.get('satellite_counts', {})
            satellite_total = result.get('satellite_total', 0)
            
            # Debug info about the received result
            logger.debug(f"RINEX completion result: {result}")
            
            # Check for missing values and use fallbacks if available
            if antenna_height is None and hasattr(self, 'base_station_data') and 'antenna_height' in self.base_station_data:
                antenna_height = self.base_station_data['antenna_height']
                antenna_height_units = self.base_station_data.get('antenna_height_units', 'ft')
                logger.info(f"Using antenna height from base station data: {antenna_height} {antenna_height_units}")
            elif antenna_height is None:
                # Default fallback value
                antenna_height = self.antenna_height_input.value()
                antenna_height_units = self.antenna_height_units if hasattr(self, 'antenna_height_units') else 'ft'
                logger.info(f"Using antenna height from UI: {antenna_height} {antenna_height_units}")
            
            # Final check for missing critical values
            if not all([rinex_start, rinex_end, base_lat, base_lon, base_ellh, antenna_height]):
                missing = []
                if not rinex_start: missing.append("rinex_start")
                if not rinex_end: missing.append("rinex_end")
                if not base_lat: missing.append("base_lat")
                if not base_lon: missing.append("base_lon")
                if not base_ellh: missing.append("base_ellh")
                if not antenna_height: missing.append("antenna_height")
                raise ValueError(f"Missing required RINEX data fields: {', '.join(missing)}")
            
            # Store time information
            self.rinex_start = rinex_start
            self.rinex_end = rinex_end
            
            # IMPORTANT: We're no longer creating the corrected RINEX file here
            # Store information needed for later processing
            self.rinex_file = self.rinex_input.text()
            
            # Update satellite info
            if hasattr(self, 'satellite_info_label'):
                if satellite_total > 0:
                    sat_text = f"Total: {satellite_total} - "
                    sat_details = []
                    for system, count in satellite_counts.items():
                        if count > 0:
                            sat_details.append(f"{system}: {count}")
                    sat_text += ", ".join(sat_details)
                    self.satellite_info_label.setText(sat_text)
                    self.satellite_info_label.setStyleSheet("color: white;")
                else:
                    # Try to count satellite systems from header directly
                    try:
                        header = gr.rinexheader(self.rinex_file)
                        if isinstance(header, dict):
                            systems = []
                            if 'G' in str(header): systems.append("GPS")
                            if 'R' in str(header): systems.append("GLONASS")
                            if 'E' in str(header): systems.append("Galileo")
                            if 'C' in str(header): systems.append("BeiDou")
                            if 'J' in str(header): systems.append("QZSS")
                            
                            if systems:
                                self.satellite_info_label.setText(f"Systems: {', '.join(systems)}")
                                self.satellite_info_label.setStyleSheet("color: white;")
                    except Exception as e:
                        logger.warning(f"Error getting satellite systems from header: {str(e)}")
            
            # Update the RINEX timing display
            self.update_rinex_timing_display()
            
            # Start flight analysis only
            project_dir = self.dir_input.text() if hasattr(self, 'dir_input') else self.project_dir
            
            self.flight_processor = FlightProcessor(
                project_dir,
                rinex_start,
                rinex_end,
                self
            )
            self.flight_processor.progress.connect(self.update_status)
            self.flight_processor.error.connect(self.handle_error)
            self.flight_processor.finished.connect(self.handle_flight_processor_complete)
            self.flight_processor.start()
            
            # Update status
            self.rinex_status_label.setText("Status: RINEX data ready for processing")
            self.rinex_status_label.setStyleSheet("color: #4CAF50;")  # Green for success
            
            # Enable processing button
            self.process_button.setEnabled(True)
            
        except Exception as e:
            logger.error(f"Error processing RINEX completion: {str(e)}")
            logger.error(traceback.format_exc())  # Add full traceback for better debugging
            self.handle_error(f"Error processing RINEX completion: {str(e)}")
            self.rinex_status_label.setText(f"Status: Error - {str(e)}")
            self.rinex_status_label.setStyleSheet("color: #f44336;")  # Red for error

    def setup_ui(self):
        self.setGeometry(100, 100, 1200, 800)
        
        # Apply dark theme
        self.setStyleSheet("""
            QMainWindow, QDialog {
                background-color: #212121;
                color: white;
            }
            QLabel, QCheckBox, QRadioButton, QSpinBox, QDoubleSpinBox {
                color: white;
            }
            QLineEdit, QComboBox, QSpinBox, QDoubleSpinBox {
                background-color: #424242;
                color: white;
                border: 1px solid #555;
                padding: 5px;
                border-radius: 2px;
            }
            QComboBox::drop-down {
                border: 0px;
                background-color: #424242;
            }
            QComboBox QAbstractItemView {
                background-color: #333333;
                color: white;
                selection-background-color: #4CAF50;
                selection-color: white;
                outline: 0;
            }
            QPushButton {
                background-color: #4CAF50;
                color: white;
                border: none;
                padding: 8px 16px;
                border-radius: 4px;
            }
            QPushButton:hover {
                background-color: #66BB6A;
            }
            QPushButton:disabled {
                background-color: #757575;
                color: #BDBDBD;
            }
            QGroupBox {
                color: white;
                border: 1px solid #555;
                border-radius: 4px;
                margin-top: 20px;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px;
            }
            QScrollBar:vertical {
                border: none;
                background-color: #424242;
                width: 12px;
                margin: 0px;
            }
            QScrollBar::handle:vertical {
                background-color: #666666;
                min-height: 20px;
                border-radius: 6px;
            }
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {
                border: none;
                background: none;
            }
            QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical {
                background: none;
            }
        """)
        
        # Create main widget and layout
        main_widget = QWidget()
        main_layout = QVBoxLayout(main_widget)
        main_layout.setContentsMargins(20, 20, 20, 20)
        main_layout.setSpacing(15)
        self.setCentralWidget(main_widget)
        
        # --- Title ---
        title_layout = QVBoxLayout()
        title_label = QLabel("Base Point Correction Tool")
        title_label.setStyleSheet("font-size: 24px; font-weight: bold; color: #4CAF50;")
        title_label.setAlignment(Qt.AlignCenter)
        title_layout.addWidget(title_label)
        
        main_layout.addLayout(title_layout)
        
        # --- Project directory selection ---
        dir_group = QGroupBox("Project Directory")
        dir_group.setStyleSheet("QGroupBox { font-weight: bold; }")
        dir_layout = QVBoxLayout(dir_group)
        
        dir_input_layout = QHBoxLayout()
        dir_input_label = QLabel("Project Directory:")
        self.dir_input = QLineEdit()
        self.dir_input.setPlaceholderText("Select a directory containing Emlid-All Columns CSV Export, Emlid Rinex Folder and DJI LiDAR Flight Folders")
        dir_browse_button = QPushButton("Browse")
        dir_browse_button.clicked.connect(self.select_project_directory)
        
        dir_input_layout.addWidget(dir_input_label)
        dir_input_layout.addWidget(self.dir_input, 1)  # Stretch factor
        dir_input_layout.addWidget(dir_browse_button)
        dir_layout.addLayout(dir_input_layout)
        
        # Coordinate system info
        coord_info_layout = QHBoxLayout()
        coord_info_label = QLabel("Detected Coordinate System:")
        self.input_coord_label = QLabel("Not detected")
        self.input_coord_label.setStyleSheet("color: #BBBBBB;")
        
        coord_info_layout.addWidget(coord_info_label)
        coord_info_layout.addWidget(self.input_coord_label, 1)  # Stretch factor
        dir_layout.addLayout(coord_info_layout)
        
        main_layout.addWidget(dir_group)
        
        # --- Base Station Configuration ---
        base_group = QGroupBox("Base Station Configuration")
        base_group.setStyleSheet("QGroupBox { font-weight: bold; }")
        base_layout = QVBoxLayout(base_group)
        
        # Base point selection
        base_point_layout = QHBoxLayout()
        base_point_label = QLabel("Base Station Point:")
        self.base_point_combo = QComboBox()
        self.base_point_combo.addItem("Select Base Point...")
        self.base_point_combo.currentIndexChanged.connect(self.on_base_point_changed)
        
        base_point_layout.addWidget(base_point_label)
        base_point_layout.addWidget(self.base_point_combo, 1)  # Stretch factor
        base_layout.addLayout(base_point_layout)
        
        # Base coordinates display
        base_coords_layout = QHBoxLayout()
        self.base_easting_label = QLabel("Easting: --")
        self.base_northing_label = QLabel("Northing: --")
        self.base_elevation_label = QLabel("Elevation: --")
        
        base_coords_layout.addWidget(self.base_easting_label)
        base_coords_layout.addWidget(self.base_northing_label)
        base_coords_layout.addWidget(self.base_elevation_label)
        base_layout.addLayout(base_coords_layout)
        
        # Antenna height input
        antenna_layout = QHBoxLayout()
        antenna_label = QLabel("Antenna Height:")
        self.antenna_height_input = QDoubleSpinBox()
        self.antenna_height_input.setRange(0, 100)
        self.antenna_height_input.setDecimals(3)
        self.antenna_height_input.setSingleStep(0.1)
        self.antenna_height_unit_label = QLabel("(m)")  # This will be updated dynamically
        self.antenna_height_warning = QLabel()  # Add warning label
        self.antenna_height_warning.setStyleSheet("color: #FFA500; font-style: italic;")  # Orange warning color
        
        antenna_layout.addWidget(antenna_label)
        antenna_layout.addWidget(self.antenna_height_input)
        antenna_layout.addWidget(self.antenna_height_unit_label)
        antenna_layout.addWidget(self.antenna_height_warning)
        base_layout.addLayout(antenna_layout)
        
        # RINEX file selection
        rinex_layout = QHBoxLayout()
        rinex_label = QLabel("RINEX Base Station File:")
        self.rinex_input = QLineEdit()
        self.rinex_input.setPlaceholderText("Select RINEX file")
        rinex_browse_button = QPushButton("Browse")
        rinex_browse_button.clicked.connect(self.select_rinex_file)
        
        rinex_layout.addWidget(rinex_label)
        rinex_layout.addWidget(self.rinex_input, 1)  # Stretch factor
        rinex_layout.addWidget(rinex_browse_button)
        base_layout.addLayout(rinex_layout)
        
        # RINEX Status
        rinex_status_layout = QHBoxLayout()
        rinex_status_text = QLabel("Status:")
        self.rinex_status_label = QLabel("No file loaded")
        self.rinex_status_label.setStyleSheet("color: #BBBBBB;")
        
        rinex_status_layout.addWidget(rinex_status_text)
        rinex_status_layout.addWidget(self.rinex_status_label, 1)  # Stretch factor
        base_layout.addLayout(rinex_status_layout)
        
        # Position correction info
        position_correction_layout = QHBoxLayout()
        position_correction_text = QLabel("Position Correction:")
        self.position_correction_label = QLabel("Not applied")
        self.position_correction_label.setStyleSheet("color: #BBBBBB;")
        
        position_correction_layout.addWidget(position_correction_text)
        position_correction_layout.addWidget(self.position_correction_label, 1)  # Stretch factor
        base_layout.addLayout(position_correction_layout)
        
        # Satellite info
        satellite_info_layout = QHBoxLayout()
        satellite_info_text = QLabel("Satellites:")
        self.satellite_info_label = QLabel("No data")
        self.satellite_info_label.setStyleSheet("color: #BBBBBB;")
        
        satellite_info_layout.addWidget(satellite_info_text)
        satellite_info_layout.addWidget(self.satellite_info_label, 1)  # Stretch factor
        base_layout.addLayout(satellite_info_layout)
        
        main_layout.addWidget(base_group)
        
        # --- Output CSV Configuration ---
        output_group = QGroupBox("Output CSV Configuration")
        output_group.setStyleSheet("""
            QGroupBox {
                border: 1px solid #555;
                border-radius: 5px;
                margin-top: 10px;
                font-weight: bold;
                color: white;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px;
            }
        """)
        output_layout = QVBoxLayout(output_group)
        
        # Coordinate System Selection
        coord_sys_layout = QHBoxLayout()
        coord_sys_label = QLabel("Coordinate System:")
        self.coord_sys_toggle = QComboBox()
        self.coord_sys_toggle.addItems(["Local", "Global (WGS84)"])
        self.coord_sys_toggle.currentIndexChanged.connect(self.on_coord_sys_changed)
        
        # Add detected coordinate system label
        self.detected_cs_label = QLabel("")
        self.detected_cs_label.setStyleSheet("color: #888;")
        
        coord_sys_layout.addWidget(coord_sys_label)
        coord_sys_layout.addWidget(self.coord_sys_toggle)
        output_layout.addLayout(coord_sys_layout)
        output_layout.addWidget(self.detected_cs_label)
        
        # Global system height unit option (initially hidden)
        self.global_height_container = QWidget()
        self.global_height_layout = QHBoxLayout(self.global_height_container)
        self.global_height_layout.setContentsMargins(0, 0, 0, 0)
        self.global_height_label = QLabel("Ellipsoidal Height:")
        self.global_height_combo = QComboBox()
        self.global_height_combo.addItems(["US survey feet", "meters"])
        self.global_height_layout.addWidget(self.global_height_label)
        self.global_height_layout.addWidget(self.global_height_combo)
        self.global_height_container.setVisible(False)
        output_layout.addWidget(self.global_height_container)
        
        # Column Order Selection
        col_order_layout = QHBoxLayout()
        col_order_label = QLabel("Column Order:")
        self.col_order_toggle = QComboBox()
        
        # Initialize with local coordinate system options
        self.col_order_toggle.addItems([
            "Name, Easting, Northing, Elevation",
            "Name, Northing, Easting, Elevation"
        ])
        
        col_order_layout.addWidget(col_order_label)
        col_order_layout.addWidget(self.col_order_toggle)
        output_layout.addLayout(col_order_layout)
        
        main_layout.addWidget(output_group)
        
        # --- RINEX timing information ---
        timing_group = QGroupBox("RINEX and Flight Timing Analysis")
        timing_group.setStyleSheet("QGroupBox { font-weight: bold; }")
        timing_layout = QVBoxLayout(timing_group)
        
        # Coverage status
        coverage_layout = QHBoxLayout()
        self.coverage_status_label = QLabel("Coverage Status: Unknown")
        self.coverage_status_label.setStyleSheet("""
            padding: 5px 10px;
            font-weight: bold;
            background-color: #333333;
            color: #BBBBBB;
            border-radius: 4px;
            border: 1px solid #555555;
        """)
        coverage_layout.addWidget(self.coverage_status_label)
        coverage_layout.addStretch()
        timing_layout.addLayout(coverage_layout)
        
        # Timing information text
        self.rinex_time_label = QTextBrowser()
        self.rinex_time_label.setPlaceholderText("RINEX timing information will be displayed here")
        self.rinex_time_label.setReadOnly(True)
        self.rinex_time_label.setStyleSheet("background-color: #424242; color: white;")
        # Make the text browser expand to fill available space
        size_policy = QSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.rinex_time_label.setSizePolicy(size_policy)
        timing_layout.addWidget(self.rinex_time_label)
        
        # Visual timeline for RINEX and flight missions
        self.timeline_widget = QWidget()
        self.timeline_widget.setFixedHeight(100)
        self.timeline_widget.setMinimumWidth(300)
        self.timeline_widget.setStyleSheet("background-color: #424242; border-radius: 4px;")
        self.timeline_layout = QVBoxLayout(self.timeline_widget)
        self.timeline_layout.setContentsMargins(10, 5, 10, 5)
        
        # Add the timeline widget to the timing group
        timing_layout.addWidget(self.timeline_widget)
        
        main_layout.addWidget(timing_group)
        
        # --- Processing and Export ---
        process_group = QGroupBox("Processing")
        process_group.setStyleSheet("QGroupBox { font-weight: bold; }")
        process_layout = QVBoxLayout(process_group)
        
        # Buttons
        button_layout = QHBoxLayout()
        
        self.process_button = QPushButton("Process PPK Data")
        self.process_button.clicked.connect(self.process_button_clicked)
        self.process_button.setToolTip("Perform Post-Processing Kinematic (PPK) calculations with RINEX")
        self.process_button.setStyleSheet("""
            background-color: #2196F3;
            color: white;
                font-weight: bold;
            padding: 10px 20px;
        """)
        
        self.export_button = QPushButton("Export CSV")
        self.export_button.clicked.connect(self.export_csv)
        self.export_button.setToolTip("Export data with coordinate transformation (processing optional)")
        self.export_button.setEnabled(True)  # Enable by default
        
        button_layout.addStretch()
        button_layout.addWidget(self.process_button)
        button_layout.addWidget(self.export_button)
        button_layout.addStretch()
        process_layout.addLayout(button_layout)

        # Add processing group to main layout
        main_layout.addWidget(process_group)

        # Status bar for messages
        self.statusBar().showMessage("Ready")
        self.statusBar().setStyleSheet("""
            QStatusBar {
                background-color: #333333;
                color: white;
                padding: 5px;
                font-size: 13px;
                border-top: 1px solid #555555;
            }
        """)

        # Initialize instance variables
        self.base_points_df = None
        self.detected_files = []
        self.processed_data = None
        self.original_rinex_path = None
        self.corrected_rinex_path = None

    def on_coord_sys_changed(self, index):
        """Handle coordinate system toggle changes"""
        is_global = index == 1  # Global (WGS84) is index 1
        self.global_height_container.setVisible(is_global)
        
        # Update column order options based on coordinate system
        self.col_order_toggle.clear()
        if is_global:
            self.col_order_toggle.addItems([
                "Name, Latitude, Longitude, Elevation",
                "Name, Longitude, Latitude, Elevation"
            ])
            self.col_order_toggle.setEnabled(True)  # Enable for global coordinates
        else:
            self.col_order_toggle.addItems([
                "Name, Easting, Northing, Elevation",
                "Name, Northing, Easting, Elevation"
            ])
            self.col_order_toggle.setEnabled(True)
        
        # Update the detected CS label
        if hasattr(self, 'detected_cs_name'):
            if not is_global:
                self.detected_cs_label.setText(f"Detected: {self.detected_cs_name}")
            else:
                self.detected_cs_label.setText("")

    def select_project_directory(self):
        """Open dialog to select project directory"""
        directory = QFileDialog.getExistingDirectory(self, "Select Project Directory")
        if directory:
            try:
                self.dir_input.setText(directory)
                self.project_dir = directory  # Store as instance variable
                logger.info(f"Selected project directory: {directory}")
                self.statusBar().showMessage(f"Selected project directory: {directory}")
                
                # Reset any previously loaded data
                self.base_points_df = None
                self.detected_files = []
                self.base_point_combo.clear()
                self.base_point_combo.addItem("Select Base Point...")
                
                # Initialize fields
                self.base_easting_label.setText("Easting: --")
                self.base_northing_label.setText("Northing: --")
                self.base_elevation_label.setText("Elevation: --")
                self.rinex_status_label.setText("Status: No file loaded")
                self.rinex_status_label.setStyleSheet("color: #BBBBBB;")
                self.satellite_info_label.setText("No data")
                
                # Clear RINEX path
                if hasattr(self, 'original_rinex_path'):
                    del self.original_rinex_path
                if hasattr(self, 'corrected_rinex_path'):
                    del self.corrected_rinex_path
                    
                # Detect coordinate system and load base points
                self.detect_coordinate_system()
                
                # If we have base points, enable the UI elements
                if self.base_points_df is not None and len(self.base_points_df) > 0:
                    self.statusBar().showMessage(f"Found {len(self.base_points_df)} potential base points")
                    
            except Exception as e:
                logger.error(f"Error selecting project directory: {str(e)}")
                traceback.print_exc()
                self.statusBar().showMessage(f"Error: {str(e)}")
                QMessageBox.critical(
                    self,
                    "Error",
                    f"Failed to initialize project directory: {str(e)}"
                )

    def select_rinex_file(self):
        """Open dialog to select RINEX base station file"""
        file_name, _ = QFileDialog.getOpenFileName(
            self,
            "Select RINEX Base Station File",
            "",
            "RINEX Files (*.??o);;All Files (*.*)"
        )
        if file_name:
            self.rinex_input.setText(file_name)
            
            # Try to find closest base point first
            closest_point = self.find_closest_base_point()
            
            # If user didn't select the closest point or none was found
            if self.base_point_combo.currentIndex() == 0:
                # Inform user to select a base station point
                self.statusBar().showMessage("Please select a base station point before loading RINEX data")
                self.rinex_status_label.setText("Status: Select a base station point first")
                self.rinex_status_label.setStyleSheet("color: #FF9800; font-weight: bold;")
                if not closest_point:
                    QMessageBox.information(
                        self,
                        "Base Station Required",
                        "Please select a base station point before loading RINEX data."
                    )
            else:
                # Load the RINEX file after selecting it
                self.read_rinex_data()

    def detect_coordinate_system(self):
        """Detect coordinate system from CSV files and populate base points"""
        try:
            # Find all CSV files
            csv_files = []
            for file in os.listdir(self.project_dir):
                if file.endswith('.csv') and not file.startswith('processed_'):
                    csv_files.append(os.path.join(self.project_dir, file))
            
            if not csv_files:
                raise ValueError("No CSV files found in project directory")
            
            # Read the first CSV file to detect coordinate system and base points
            first_csv = csv_files[0]
            df = pd.read_csv(first_csv)
            logger.info(f"Analyzing CSV file: {os.path.basename(first_csv)}")
            
            # Store the original dataframe
            self.base_points_df = df.copy()
            
            # Check for CS name column and detect units
            if 'CS name' in df.columns:
                self.coordinate_system_name = df['CS name'].iloc[0]
                logger.info(f"Detected coordinate system from CS name: {self.coordinate_system_name}")
                
                # Detect if coordinate system uses feet
                cs_name_lower = self.coordinate_system_name.lower()
                self.is_feet_based = any(feet_indicator in cs_name_lower 
                                       for feet_indicator in ['feet', 'ft', 'usft', 'ftus'])
                
                logger.info(f"Coordinate system uses {'feet' if self.is_feet_based else 'meters'}")
                self.detected_cs_label.setText(f"Detected: {self.coordinate_system_name}")
            else:
                self.coordinate_system_name = "Unknown Coordinate System"
                self.is_feet_based = False
                logger.warning("No CS name column found in CSV")
                self.detected_cs_label.setText("No coordinate system detected")
            
            # Check for antenna height units
            if 'Antenna height units' in df.columns:
                # Get the first non-null antenna height unit
                antenna_units = df['Antenna height units'].dropna().iloc[0] if not df['Antenna height units'].isna().all() else 'm'
                self.antenna_height_units = antenna_units
                logger.info(f"Detected antenna height units: {antenna_units}")
            else:
                # Default to meters if no units column
                self.antenna_height_units = 'm'
                logger.info("No antenna height units column found, defaulting to meters")
            
            # Update UI with detected units
            if hasattr(self, 'antenna_height_unit_label'):
                self.antenna_height_unit_label.setText(self.antenna_height_units)
            
            # Update the input coordinate system label
            if hasattr(self, 'input_coord_label'):
                unit_text = " (US Survey Feet)" if self.is_feet_based else " (meters)"
                self.input_coord_label.setText(f"{self.coordinate_system_name}{unit_text}")
                self.input_coord_label.setStyleSheet("color: white;")
            
            # Log the available columns
            logger.info(f"Available columns: {', '.join(df.columns)}")
            
            # Update base points combo box if we have the required columns
            required_cols = ['Name', 'Easting', 'Northing', 'Elevation']
            if all(col in df.columns for col in required_cols):
                logger.info(f"Found {len(df)} potential base points")
                self.update_base_points_combo()
            else:
                missing_cols = [col for col in required_cols if col not in df.columns]
                logger.warning(f"Missing required columns: {', '.join(missing_cols)}")
                raise ValueError(f"CSV file missing required columns: {', '.join(missing_cols)}")

            # Look for RINEX files in the project directory after base points are loaded
            rinex_files = self.find_rinex_files(self.project_dir)
            
            # If we found RINEX files, try to find the closest base point
            if rinex_files:
                logger.info("Found RINEX files, finding closest base point")
                QTimer.singleShot(100, self.find_closest_base_point)  # Delay to ensure UI is updated
                
        except Exception as e:
            logger.error(f"Error detecting coordinate system: {str(e)}")
            self.statusBar().showMessage(f"Error detecting coordinate system: {str(e)}")
            if hasattr(self, 'input_coord_label'):
                self.input_coord_label.setText(f"Error: {str(e)}")
                self.input_coord_label.setStyleSheet("color: #f44336;")  # Red error color

    def update_base_points_combo(self):
        """Update the base points combo box with points from the DataFrame"""
        self.base_point_combo.clear()
        self.base_point_combo.addItem("Select Base Point...")
        for idx, row in self.base_points_df.iterrows():
            try:
                point_name = str(row['Name'])
                self.base_point_combo.addItem(point_name)
                logger.debug(f"Added point: {point_name}")
            except Exception as e:
                logger.warning(f"Error adding point at index {idx}: {str(e)}")
                continue
        self.base_point_combo.setCurrentIndex(0)

    def on_base_point_changed(self, index):
        """Handle base point selection"""
        if index > 0:  # Skip the placeholder item
            try:
                point_name = self.base_point_combo.currentText()
                matching_points = self.base_points_df[self.base_points_df['Name'] == point_name]
                
                if matching_points.empty:
                    raise ValueError(f"Could not find point with name: {point_name}")
                    
                point_data = matching_points.iloc[0]
                
                # Store the base station data with all necessary coordinates
                self.base_station_data = {
                    'name': point_name,
                    'easting': float(point_data['Easting']),
                    'northing': float(point_data['Northing']),
                    'elevation': float(point_data['Elevation']),
                    'latitude': float(point_data['Latitude']) if 'Latitude' in point_data else None,
                    'longitude': float(point_data['Longitude']) if 'Longitude' in point_data else None,
                    'ellipsoidal_height': float(point_data['Ellipsoidal height']) if 'Ellipsoidal height' in point_data else None
                }
                
                # Update the base station coordinates display
                self.update_base_position_info()
                
                # Check if the CSV contains antenna height and update the UI
                antenna_height_found = False
                if 'Antenna height' in point_data and not pd.isna(point_data['Antenna height']):
                    try:
                        antenna_height = float(point_data['Antenna height'])
                        # Get units from CSV or default to feet
                        csv_units = str(point_data['Antenna height units']).lower() if 'Antenna height units' in point_data else 'ft'
                        
                        # Use the units directly from CSV without any conversion
                        self.antenna_height_units = csv_units
                        self.antenna_height_input.setValue(antenna_height)
                        
                        if hasattr(self, 'antenna_height_unit_label'):
                            self.antenna_height_unit_label.setText(csv_units)
                            
                        # Store antenna height in base_station_data with original units
                        self.base_station_data['antenna_height'] = antenna_height
                        self.base_station_data['antenna_height_units'] = csv_units
                            
                        logger.info(f"Updated antenna height from CSV: {antenna_height} {csv_units}")
                        antenna_height_found = True
                        self.antenna_height_warning.setText("")  # Clear any warning
                    except (ValueError, TypeError) as e:
                        logger.warning(f"Could not convert antenna height value: {str(e)}")
                        antenna_height_found = False
                
                if not antenna_height_found:
                    # Set default values based on coordinate system units
                    if hasattr(self, 'is_feet_based') and self.is_feet_based:
                        default_height = 7.001  # Default in feet
                        default_units = 'ft'
                    else:
                        default_height = 2.134  # Default in meters
                        default_units = 'm'
                    
                    self.antenna_height_units = default_units
                    self.antenna_height_input.setValue(default_height)
                    if hasattr(self, 'antenna_height_unit_label'):
                        self.antenna_height_unit_label.setText(default_units)
                    
                    # Store default antenna height in base_station_data
                    self.base_station_data['antenna_height'] = default_height
                    self.base_station_data['antenna_height_units'] = default_units
                    
                    # Show warning about default value
                    warning_text = f"No antenna height found. Using default: {default_height} {default_units}"
                    self.antenna_height_warning.setText(warning_text)
                    logger.info(f"Set default antenna height to {default_height} {default_units}")
                
                # If we have a RINEX file, calculate position correction immediately
                if self.rinex_input.text() and os.path.exists(self.rinex_input.text()):
                    rinex_file = self.rinex_input.text()
                    try:
                        # Get current position from RINEX header
                        header = gr.rinexheader(rinex_file)
                        current_pos = None
                        
                        if isinstance(header, dict):
                            current_pos = header.get('position', [0, 0, 0])
                        else:
                            # Try to parse position from header string
                            pos_match = re.search(r'APPROX POSITION XYZ\s+([-\d.]+)\s+([-\d.]+)\s+([-\d.]+)', str(header))
                            if pos_match:
                                current_pos = [float(pos_match.group(1)), float(pos_match.group(2)), float(pos_match.group(3))]
                        
                        if current_pos and len(current_pos) >= 3:
                            # Convert current ECEF to lat/lon/height
                            transformer = pyproj.Transformer.from_crs('EPSG:4978', 'EPSG:4326', always_xy=True)
                            current_lon, current_lat, current_height = transformer.transform(
                                current_pos[0], current_pos[1], current_pos[2]
                            )
                            
                            # Calculate shifts
                            horizontal_shift = haversine(
                                self.base_station_data['longitude'],
                                self.base_station_data['latitude'],
                                current_lon,
                                current_lat
                            )
                            
                            # Convert heights to meters if needed
                            base_ellh_m = self.base_station_data['ellipsoidal_height']
                            if self.is_feet_based:
                                base_ellh_m = base_ellh_m / 3.28083333333333
                                
                            vertical_shift = abs(base_ellh_m - current_height)
                            
                            # Update position correction display
                            position_shift_text = format_shift_display(horizontal_shift, vertical_shift)
                            total_shift = sqrt(horizontal_shift**2 + vertical_shift**2)
                            
                            if total_shift > 5.0:
                                self.position_correction_label.setText(f"LARGE SHIFT - {position_shift_text}")
                                self.position_correction_label.setStyleSheet("color: #FF9800; font-weight: bold;")  # Orange warning
                            else:
                                self.position_correction_label.setText(f"{position_shift_text}")
                                self.position_correction_label.setStyleSheet("color: #4CAF50; font-weight: bold;")  # Green success
                                
                    except Exception as e:
                        logger.warning(f"Could not calculate position correction: {str(e)}")
                        self.position_correction_label.setText("Could not calculate position correction")
                        self.position_correction_label.setStyleSheet("color: #f44336;")  # Red for error
                
                # Check if we already have a RINEX file and load it
                if self.rinex_input.text():
                    self.read_rinex_data()
                    
                # Enable process button
                self.process_button.setEnabled(True)
                # Keep export button enabled (allows direct coordinate transformation without PPK)
                self.export_button.setEnabled(True)
                
            except Exception as e:
                logger.error(f"Error updating base point info: {str(e)}")
                logger.error(traceback.format_exc())
                self.statusBar().showMessage(f"Error: {str(e)}")
        else:
            # Reset UI elements when "Select Base Point..." is chosen
            self.base_easting_label.setText("Easting: --")
            self.base_northing_label.setText("Northing: --")
            self.base_elevation_label.setText("Elevation: --")
            self.rinex_status_label.setText("Status: Select a base station point")
            self.rinex_status_label.setStyleSheet("color: #BBBBBB;")
            self.process_button.setEnabled(False)
            self.position_correction_label.setText("Not applied")
            self.position_correction_label.setStyleSheet("color: #BBBBBB;")
            
            # Clear any existing base station data
            if hasattr(self, 'base_station_data'):
                delattr(self, 'base_station_data')

    def find_rinex_files(self, directory):
        """Find RINEX files in the project directory and subdirectories"""
        rinex_files = []
        try:
            # Walk through directory and subdirectories
            for root, dirs, files in os.walk(directory):
                for file in files:
                    # Check for RINEX observation files with common extensions
                    if (file.endswith(('O', 'o', '.obs', '.OBS')) or 
                        (len(file) > 3 and file[-3] == 'O' and file[-2:].isdigit()) and
                        not file.startswith('corrected_')):
                        full_path = os.path.join(root, file)
                        rinex_files.append(full_path)
                        logger.info(f"Found RINEX file: {file} in {root}")
            
            if rinex_files:
                # Use the first RINEX file found
                self.rinex_input.setText(rinex_files[0])
                logger.info(f"Set RINEX input to: {rinex_files[0]}")
                self.statusBar().showMessage(f"Found {len(rinex_files)} RINEX files")
            else:
                logger.warning("No RINEX files found in project directory or subdirectories")
                self.statusBar().showMessage("No RINEX files found in project directory")
                
            return rinex_files
                
        except Exception as e:
            logger.error(f"Error finding RINEX files: {str(e)}")
            self.statusBar().showMessage(f"Error finding RINEX files: {str(e)}")
            return []

    def validate_inputs(self):
        """Validate all required inputs are present and valid"""
        if not hasattr(self, 'project_dir') or not self.project_dir:
            raise ValueError("Please select a project directory first")
            
        if not self.rinex_input.text():
            raise ValueError("Please select a RINEX base station file")
            
        if self.base_point_combo.currentIndex() == 0:
            raise ValueError("Please select a base station point")
            
        # Validate base station coordinates
        if not hasattr(self, 'base_points_df') or self.base_points_df is None:
            raise ValueError("Base station coordinates are incomplete")
            
        # Get antenna height
        antenna_height = self.antenna_height_input.value()
        
        # Convert antenna height to meters if needed (RINEX expects meters)
        if self.antenna_height_unit_label.text() == "(ft)":
            antenna_height = antenna_height * 0.3048  # Convert feet to meters
            logger.debug(f"Converting antenna height from {self.antenna_height_input.value()} ft to {antenna_height} m")
            
        return antenna_height

    def get_active_rinex_path(self):
        """Get the actual RINEX file to use (either original or corrected)"""
        if hasattr(self, 'corrected_rinex_path') and self.corrected_rinex_path:
            return self.corrected_rinex_path
        elif hasattr(self, 'original_rinex_path') and self.original_rinex_path:
            return self.original_rinex_path
        return None
            
    def process_button_clicked(self):
        """Handle process button click"""
        try:
            # Validate inputs
            antenna_height = self.validate_inputs()
            
            # Get RINEX file path
            rinex_file = self.get_active_rinex_path()
            if not rinex_file:
                raise ValueError("No RINEX file selected")
            
            # Get base station coordinates from selected point
            base_point = self.base_point_combo.currentText()
            if not base_point or base_point == "Select Base Point...":
                raise ValueError("Please select a base station point")
            
            base_data = self.base_points_df[self.base_points_df['Name'] == base_point].iloc[0]
            
            # Convert heights to meters and combine
            ant_height_meters = (
                feet_to_meters(antenna_height) 
                if self.antenna_height_units == 'ft'
                else antenna_height
            )
            
            ellh_meters = (
                feet_to_meters(base_data['Ellipsoidal height'])
                if self.is_feet_based
                else base_data['Ellipsoidal height']
            )
            
            total_height_meters = ellh_meters + ant_height_meters
            
            # Convert to ECEF
            x, y, z = convert_to_ecef(
                base_data['Latitude'],
                base_data['Longitude'],
                total_height_meters
            )
            
            logger.info(f"Converting coordinates:")
            logger.info(f"Input - Lat: {base_data['Latitude']}, Lon: {base_data['Longitude']}, Height: {total_height_meters}m")
            logger.info(f"Output ECEF - X: {x:.4f}, Y: {y:.4f}, Z: {z:.4f}")
            
            # Create temporary file for updated RINEX
            temp_rinex = os.path.join(os.path.dirname(rinex_file), "temp_rinex.tmp")
            update_rinex_header(rinex_file, temp_rinex, x, y, z)
            
            # Process each flight folder
            project_dir = self.dir_input.text()
            processed_count = 0
            
            for item in os.listdir(project_dir):
                folder_path = os.path.join(project_dir, item)
                if os.path.isdir(folder_path):
                    # Find RTK file in folder
                    rtk_files = [f for f in os.listdir(folder_path) if f.endswith('.RTK')]
                    if rtk_files:
                        rtk_base_name = os.path.splitext(rtk_files[0])[0]
                        obs_file = os.path.join(folder_path, f"{rtk_base_name}.OBS")
                        
                        # Copy and rename updated RINEX file
                        shutil.copy2(temp_rinex, obs_file)
                        logger.info(f"Created OBS file: {obs_file}")
                        processed_count += 1
            
            # Clean up temporary file
            os.remove(temp_rinex)
            
            # Update status
            self.statusBar().showMessage(f"Successfully processed {processed_count} flight folders")
            QMessageBox.information(
                self,
                "Processing Complete",
                f"Successfully created OBS files in {processed_count} flight folders."
            )
            
        except Exception as e:
            logger.error(f"Error in PPK processing: {str(e)}")
            logger.error(traceback.format_exc())
            self.handle_error(str(e))

    def read_rinex_data(self):
        """Read and process RINEX base station data"""
        try:
            # Validate inputs
            rinex_file = self.rinex_input.text()
            if not rinex_file or not os.path.exists(rinex_file):
                raise ValueError("Please select a valid RINEX file")
                
            # Store the RINEX file path as instance variable
            self.rinex_file = rinex_file
            self.original_rinex_path = rinex_file
                
            # Check for base station data
            if not hasattr(self, 'base_station_data'):
                raise ValueError("Please select a base station point first")
            
            # Validate base station coordinates
            if (self.base_station_data['latitude'] is None or 
                self.base_station_data['longitude'] is None or 
                self.base_station_data['ellipsoidal_height'] is None):
                raise ValueError("Base station coordinates are incomplete")
            
            # Get antenna height from UI
            antenna_height = self.antenna_height_input.value()
            
            # Convert antenna height to meters if needed (RINEX expects meters)
            if self.antenna_height_units == 'ft':
                antenna_height = antenna_height * 0.3048  # Convert feet to meters
                logger.debug(f"Converting antenna height from {self.antenna_height_input.value()} ft to {antenna_height} m")
            
            # Log the values being used
            logger.debug(f"RINEX processing parameters:")
            logger.debug(f"  Base latitude: {self.base_station_data['latitude']}")
            logger.debug(f"  Base longitude: {self.base_station_data['longitude']}")
            logger.debug(f"  Base ellipsoidal height: {self.base_station_data['ellipsoidal_height']}")
            logger.debug(f"  Original antenna height: {self.antenna_height_input.value()} {self.antenna_height_units}")
            logger.debug(f"  Converted antenna height: {antenna_height} m")
            logger.debug(f"  Coordinate system: {self.coordinate_system_name}")
            logger.debug(f"  Using {'US Survey Feet' if self.is_feet_based else 'meters'} for coordinates")
            
            # Start background thread for RINEX loading
            self.rinex_worker = RinexLoadWorker(
                rinex_file,
                self.base_station_data['latitude'],
                self.base_station_data['longitude'],
                self.base_station_data['ellipsoidal_height'],
                antenna_height,  # Already converted to meters
                'm',  # Always pass meters to RINEX processor
                'm' if not self.is_feet_based else 'ft',  # Pass coordinate system units
                self  # Pass parent for proper cleanup
            )
            
            self.rinex_worker.progress.connect(self.update_status)
            self.rinex_worker.error.connect(self.handle_error)
            self.rinex_worker.finished.connect(self.handle_rinex_completion)
            self.rinex_worker.start()
            
            # Update status
            self.rinex_status_label.setText("Status: Loading RINEX data...")
            self.rinex_status_label.setStyleSheet("color: #2196F3;")  # Blue for processing
            
        except Exception as e:
            logger.error(f"Error reading RINEX data: {str(e)}")
            self.statusBar().showMessage(f"Error: {str(e)}")
            self.rinex_status_label.setText(f"Status: Error - {str(e)}")
            self.rinex_status_label.setStyleSheet("color: #f44336;")  # Red for error
            QMessageBox.critical(
                self,
                "RINEX Processing Error",
                f"Failed to process RINEX data: {str(e)}"
            )

    def update_status(self, status):
        """Update progress status during RINEX loading"""
        self.rinex_status_label.setText(f"Status: {status}")
        self.statusBar().showMessage(f"RINEX processing: {status}")
    
    def handle_error(self, error_msg):
        """Show an error message to the user"""
        QMessageBox.critical(
            self,
            "Error",
            f"An error occurred: {error_msg}"
            )
            
    def handle_flight_processor_error(self, error_msg):
        """Handle errors during flight data processing"""
        logger.error(f"Flight processor error: {error_msg}")
        self.statusBar().showMessage(f"Error processing flight data: {error_msg}")
        self.coverage_status_label.setText("Coverage Status: Error")
        self.coverage_status_label.setStyleSheet("color: #f44336;")  # Red error color
    
    def handle_flight_processor_complete(self, mission_data):
        """Handle completion of flight processing"""
        try:
            logger.debug("Flight processor completed, updating UI")
            
            # Ensure mission_data is a list
            if not isinstance(mission_data, list):
                logger.warning(f"Expected mission_data to be a list, got {type(mission_data)}")
                mission_data = []
                
            # Update the RINEX/flight timing display
            self.update_rinex_timing_display(mission_data)
            
            # Update the coverage status
            if mission_data:
                # Check if any mission has complete RINEX coverage
                has_coverage = any(mission.get('rinex_coverage', False) for mission in mission_data if isinstance(mission, dict))
                
                if has_coverage:
                    self.coverage_status_label.setText("Coverage Status: Complete")
                    self.coverage_status_label.setStyleSheet("color: #4CAF50; font-weight: bold;")  # Green for success
                else:
                    self.coverage_status_label.setText("Coverage Status: Partial or Missing")
                    self.coverage_status_label.setStyleSheet("color: #FF9800; font-weight: bold;")  # Orange for warning
            else:
                self.coverage_status_label.setText("Coverage Status: No Flight Data")
                self.coverage_status_label.setStyleSheet("color: #BBBBBB;")  # Gray for neutral
                
            # Enable processing button
            self.process_button.setEnabled(True)
            
        except Exception as e:
            logger.error(f"Error handling flight processor completion: {str(e)}")
            logger.error(traceback.format_exc())
            self.statusBar().showMessage(f"Error analyzing flight data: {str(e)}")
            
            # Still try to update UI
            self.coverage_status_label.setText("Coverage Status: Error")
            self.coverage_status_label.setStyleSheet("color: #f44336;")  # Red for error
            self.process_button.setEnabled(True)
    
    def update_rinex_timing_display(self, mission_data=None):
        """Update the RINEX timing information display"""
        if hasattr(self, 'rinex_start') and hasattr(self, 'rinex_end'):
            rinex_start = self.rinex_start
            rinex_end = self.rinex_end
            
            # Create HTML content for the RINEX time info
            html_content = "<html><body style='background-color: transparent;'>"
            
            # Add RINEX coverage information
            html_content += "<div style='margin-bottom: 12px;'>"
            html_content += "<h4 style='color: #2979FF;'>RINEX Coverage:</h4>"
            html_content += f"<p>Start: <b>{rinex_start.strftime('%Y-%m-%d %H:%M:%S')}</b> UTC<br/>"
            html_content += f"End: <b>{rinex_end.strftime('%Y-%m-%d %H:%M:%S')}</b> UTC<br/>"
            
            # Calculate actual duration
            duration_secs = (rinex_end - rinex_start).total_seconds()
            duration_hours = int(duration_secs // 3600)
            duration_mins = int((duration_secs % 3600) // 60)
            duration_str = f"{duration_hours} hours, {duration_mins} minutes"
            
            # Display duration in hours/minutes
            html_content += f"Duration: <b>{duration_str}</b></p>"
            html_content += "</div>"
            
            # Add base information
            if hasattr(self, 'base_station_data'):
                html_content += "<div style='margin-bottom: 12px;'>"
                html_content += "<h4 style='color: #2979FF;'>Base Station:</h4>"
                html_content += f"<p>Base: <b>{self.base_point_combo.currentText()}</b><br/>"
                
                # Add base coordinates
                html_content += f"Latitude: <b>{self.base_station_data['latitude']:.8f}</b><br/>"
                html_content += f"Longitude: <b>{self.base_station_data['longitude']:.8f}</b><br/>"
                
                # Handle ellipsoidal height
                if 'ellipsoidal_height' in self.base_station_data and self.base_station_data['ellipsoidal_height'] is not None:
                    ellh = self.base_station_data['ellipsoidal_height']
                    ellh_units = 'ft' if hasattr(self, 'is_feet_based') and self.is_feet_based else 'm'
                    html_content += f"Ellipsoidal Height: <b>{ellh:.4f}</b> {ellh_units}<br/>"
                
                # Safely handle antenna height
                if 'antenna_height' in self.base_station_data:
                    ant_height = self.base_station_data['antenna_height']
                    ant_units = self.base_station_data.get('antenna_height_units', 'ft')
                    html_content += f"Antenna Height: <b>{ant_height:.4f}</b> {ant_units}</p>"
                else:
                    # Fallback to UI value
                    ant_height = self.antenna_height_input.value() if hasattr(self, 'antenna_height_input') else 0.0
                    ant_units = self.antenna_height_units if hasattr(self, 'antenna_height_units') else 'ft'
                    html_content += f"Antenna Height: <b>{ant_height:.4f}</b> {ant_units}</p>"
                    
                html_content += "</div>"
            
            # Add base position correction info if available (after processing button clicked)
            if hasattr(self, 'rinex_correction_info'):
                html_content += "<div style='margin-bottom: 12px;'>"
                html_content += "<h4 style='color: #2979FF;'>Base Position Correction:</h4>"
                
                # Format the correction information
                shift = self.rinex_correction_info['shift_distance']
                shift_class = "green" if shift <= 5.0 else "orange"
                
                html_content += f"<p>Position Shift: <b style='color: {shift_class};'>{shift:.4f}</b> meters<br/>"
                
                # Add horizontal and vertical shifts
                h_shift = self.rinex_correction_info['horizontal_shift']
                v_shift = self.rinex_correction_info['vertical_shift']
                html_content += f"Horizontal Shift: <b>{h_shift:.4f}</b> meters<br/>"
                html_content += f"Vertical Shift: <b>{v_shift:.4f}</b> meters<br/>"
                
                # Add file information
                html_content += f"Original File: {os.path.basename(self.rinex_correction_info['original_file'])}<br/>"
                html_content += f"Corrected File: {os.path.basename(self.rinex_correction_info['corrected_file'])}</p>"
                html_content += "</div>"
            
            # Add flight mission information if available
            if mission_data:
                html_content += "<div style='margin-bottom: 12px;'>"
                html_content += "<h4 style='color: #2979FF;'>Flight Missions:</h4>"
                
                for i, mission in enumerate(mission_data):
                    if not isinstance(mission, dict):
                        logger.warning(f"Expected mission to be a dict, got {type(mission)}")
                        continue
                        
                    # Determine coverage status icon and color
                    coverage_status = mission.get('rinex_coverage', False)
                    coverage_icon = "✓" if coverage_status else "✗"
                    coverage_color = "#4CAF50" if coverage_status else "#f44336"
                    
                    # Get mission name safely
                    mission_name = mission.get('name', f"Mission {i+1}")
                    
                    html_content += f"<p><b>Mission {i+1}: {mission_name}</b> "
                    html_content += f"<span style='color: {coverage_color};'>{coverage_icon}</span><br/>"
                    
                    # Always prioritize photo timing data when available
                    has_photo_data = 'first_photo_readable' in mission and 'last_photo_readable' in mission
                    
                    if has_photo_data:
                        html_content += f"Photos: <b>{mission['first_photo_readable']}</b> to <b>{mission['last_photo_readable']}</b> UTC<br/>"
                        duration_minutes = mission.get('photo_duration', 0) / 60
                        photo_count = mission.get('photo_count', 0)
                        html_content += f"Duration: <b>{duration_minutes:.1f}</b> minutes"
                        if photo_count > 0:
                            html_content += f" | <b>{photo_count}</b> photos"
                        html_content += "<br/>"
                    elif 'mission_start_readable' in mission and 'mission_end_readable' in mission:
                        # Only fall back to flight controller data when photos aren't available
                        html_content += f"Flight: <b>{mission['mission_start_readable']}</b> to <b>{mission['mission_end_readable']}</b> UTC<br/>"
                        duration_minutes = mission.get('fly_time_seconds', 0) / 60
                        html_content += f"Duration: <b>{duration_minutes:.1f}</b> minutes <i>(from flight controller data)</i><br/>"
                    
                    # Show buffer information
                    if 'rinex_buffer_before' in mission and 'rinex_buffer_after' in mission:
                        buffer_before = mission['rinex_buffer_before']
                        buffer_after = mission['rinex_buffer_after']
                        
                        # Create a buffer status section
                        html_content += "<span style='display: block; margin-top: 5px;'>RINEX Buffer:</span>"
                        
                        # Before buffer
                        buffer_before_color = "green" if buffer_before >= 0 else "red"
                        html_content += f"<span style='margin-left: 10px; display: inline-block; width: 120px;'>Before mission: </span>"
                        html_content += f"<b style='color: {buffer_before_color};'>{buffer_before:.1f}</b> minutes<br/>"
                        
                        # After buffer
                        buffer_after_color = "green" if buffer_after >= 0 else "red"
                        html_content += f"<span style='margin-left: 10px; display: inline-block; width: 120px;'>After mission: </span>"
                        html_content += f"<b style='color: {buffer_after_color};'>{buffer_after:.1f}</b> minutes<br/>"
                    
                    html_content += "</p>"
                
                html_content += "</div>"
            
            html_content += "</body></html>"
            
            # Update the text browser with the HTML content
            self.rinex_time_label.setHtml(html_content)
            
            # Update the visual timeline
            self.update_visual_timeline(mission_data)
        else:
            # No RINEX data loaded yet
            self.rinex_time_label.setPlainText("RINEX timing information will be displayed here")
            self.rinex_time_label.setStyleSheet("background-color: #424242; color: #BBBBBB; border: 1px solid #555;")
            self.coverage_status_label.setText("Coverage Status: Unknown")
            self.coverage_status_label.setStyleSheet("color: #BBBBBB;")  # Gray neutral color

            # Clear the timeline when no data is available
            self.clear_timeline()

    def update_visual_timeline(self, mission_data=None):
        """Update the visual timeline display"""
        try:
            # Clear existing timeline widgets
            self.clear_timeline()
            
            if not hasattr(self, 'rinex_start') or not hasattr(self, 'rinex_end'):
                return
                
            # Get RINEX timespan
            rinex_start = self.rinex_start
            rinex_end = self.rinex_end
            rinex_duration = (rinex_end - rinex_start).total_seconds()
            
            if rinex_duration <= 0:
                logger.warning("Invalid RINEX duration for timeline")
                return
                
            # Create timeline labels
            timeline_header = QLabel("Timeline:")
            timeline_header.setStyleSheet("color: #2979FF; font-weight: bold;")
            self.timeline_layout.addWidget(timeline_header)
            
            # Create a container for the timeline bar
            timeline_container = QWidget()
            timeline_container.setFixedHeight(50)
            timeline_container_layout = QVBoxLayout(timeline_container)
            timeline_container_layout.setContentsMargins(0, 0, 0, 0)
            
            # Create the timeline bar
            timeline_bar = QWidget()
            timeline_bar.setFixedHeight(30)
            timeline_bar.setStyleSheet("background-color: #1976D2; border-radius: 3px;")
            
            # Create a layout for the timeline bar to show missions
            timeline_bar_layout = QHBoxLayout(timeline_bar)
            timeline_bar_layout.setContentsMargins(0, 0, 0, 0)
            timeline_bar_layout.setSpacing(0)
            
            # Add the timeline bar to the container
            timeline_container_layout.addWidget(timeline_bar)
            
            # Add time labels below the timeline
            time_labels_layout = QHBoxLayout()
            time_labels_layout.setContentsMargins(0, 2, 0, 0)
            
            # Start time label
            start_label = QLabel(rinex_start.strftime('%H:%M:%S'))
            start_label.setStyleSheet("color: white; font-size: 9px;")
            start_label.setAlignment(Qt.AlignLeft)
            
            # End time label
            end_label = QLabel(rinex_end.strftime('%H:%M:%S'))
            end_label.setStyleSheet("color: white; font-size: 9px;")
            end_label.setAlignment(Qt.AlignRight)
            
            # Add mid-point time label
            mid_time = rinex_start + timedelta(seconds=rinex_duration/2)
            mid_label = QLabel(mid_time.strftime('%H:%M:%S'))
            mid_label.setStyleSheet("color: white; font-size: 9px;")
            mid_label.setAlignment(Qt.AlignCenter)
            
            # Add the time labels to the layout
            time_labels_layout.addWidget(start_label)
            time_labels_layout.addStretch()
            time_labels_layout.addWidget(mid_label)
            time_labels_layout.addStretch()
            time_labels_layout.addWidget(end_label)
            
            # Add the time labels to the container
            timeline_container_layout.addLayout(time_labels_layout)
            
            # Add the timeline container to the main layout
            self.timeline_layout.addWidget(timeline_container)
            
            # Create a legend
            legend_layout = QHBoxLayout()
            
            # RINEX coverage legend
            rinex_legend = QLabel("RINEX coverage")
            rinex_legend.setStyleSheet("color: white; font-size: 10px;")
            rinex_color = QLabel()
            rinex_color.setFixedSize(12, 12)
            rinex_color.setStyleSheet("background-color: #1976D2; border-radius: 2px;")
            
            # Mission legend
            mission_legend = QLabel("Flight mission")
            mission_legend.setStyleSheet("color: white; font-size: 10px;")
            mission_color = QLabel()
            mission_color.setFixedSize(12, 12)
            mission_color.setStyleSheet("background-color: #4CAF50; border-radius: 2px;")
            
            # Add items to legend
            legend_layout.addWidget(rinex_color)
            legend_layout.addWidget(rinex_legend)
            legend_layout.addSpacing(20)
            legend_layout.addWidget(mission_color)
            legend_layout.addWidget(mission_legend)
            legend_layout.addStretch()
            
            # Add legend to the timeline layout
            self.timeline_layout.addLayout(legend_layout)
            
            # If we have mission data, show it on the timeline
            if mission_data:
                last_end_offset = 0.0
                
                for mission in mission_data:
                    if not isinstance(mission, dict):
                        continue
                        
                    # Always prioritize photo timing data when available
                    if 'first_photo_time' in mission and 'last_photo_time' in mission:
                        mission_start = mission['first_photo_time']
                        mission_end = mission['last_photo_time']
                    elif 'mission_start_utc' in mission and 'mission_end_utc' in mission:
                        mission_start = mission['mission_start_utc'] 
                        mission_end = mission['mission_end_utc']
                    else:
                        continue
                        
                    # Calculate position and width of mission segment
                    if mission_start >= rinex_start and mission_end <= rinex_end:
                        start_offset = (mission_start - rinex_start).total_seconds() / rinex_duration
                        end_offset = (mission_end - rinex_start).total_seconds() / rinex_duration
                        
                        # Add RINEX coverage (blue) for gap before this mission if needed
                        if start_offset > last_end_offset:
                            gap_width = start_offset - last_end_offset
                            rinex_segment = QWidget()
                            rinex_segment.setFixedHeight(30)
                            rinex_segment.setStyleSheet("background-color: #1976D2; border-radius: 2px;")
                            timeline_bar_layout.addWidget(rinex_segment, int(gap_width * 100))
                        
                        # Add mission segment (green/yellow)
                        mission_width = end_offset - start_offset
                        mission_marker = QWidget()
                        mission_marker.setFixedHeight(30)
                        
                        # Determine color based on coverage
                        color = "#4CAF50" if mission.get('rinex_coverage', False) else "#FFC107"
                        mission_marker.setStyleSheet(f"background-color: {color}; border-radius: 2px;")
                        
                        # Get the mission name for the tooltip
                        mission_name = mission.get('name', "Unknown mission")
                        mission_marker.setToolTip(f"{mission_name}: {mission_start.strftime('%H:%M:%S')} to {mission_end.strftime('%H:%M:%S')}")
                        
                        # Add mission marker
                        timeline_bar_layout.addWidget(mission_marker, int(mission_width * 100))
                        
                        # Update last end position
                        last_end_offset = end_offset
                
                # Add final RINEX coverage if needed
                if last_end_offset < 1.0:
                    final_width = 1.0 - last_end_offset
                    final_segment = QWidget()
                    final_segment.setFixedHeight(30)
                    final_segment.setStyleSheet("background-color: #1976D2; border-radius: 2px;")
                    timeline_bar_layout.addWidget(final_segment, int(final_width * 100))
            else:
                # If no mission data, show full RINEX coverage
                rinex_bar = QWidget()
                rinex_bar.setFixedHeight(30)
                rinex_bar.setStyleSheet("background-color: #1976D2; border-radius: 2px;")
                timeline_bar_layout.addWidget(rinex_bar)
            
        except Exception as e:
            logger.error(f"Error updating visual timeline: {str(e)}")
            logger.error(traceback.format_exc())

    def clear_timeline(self):
        """Clear the timeline layout"""
        try:
            if hasattr(self, 'timeline_layout'):
                # Remove all widgets from the layout
                while self.timeline_layout.count():
                    item = self.timeline_layout.takeAt(0)
                    if item.widget():
                        item.widget().deleteLater()
                    elif item.layout():
                        # Recursively clear layouts
                        while item.layout().count():
                            subitem = item.layout().takeAt(0)
                            if subitem.widget():
                                subitem.widget().deleteLater()
        except Exception as e:
            logger.error(f"Error clearing timeline: {str(e)}")
            logger.error(traceback.format_exc())

    def update_base_position_info(self):
        """Update the base station position information display"""
        try:
            if not hasattr(self, 'base_station_data'):
                return
                
            # Format coordinates with appropriate precision
            precision = 4 if self.is_feet_based else 3
            
            # Get the appropriate unit label
            unit_label = 'ft' if self.is_feet_based else 'm'
            
            # Update labels with values and units
            self.base_easting_label.setText(f"Easting: {self.base_station_data['easting']:.{precision}f} {unit_label}")
            self.base_northing_label.setText(f"Northing: {self.base_station_data['northing']:.{precision}f} {unit_label}")
            self.base_elevation_label.setText(f"Elevation: {self.base_station_data['elevation']:.{precision}f} {unit_label}")
            
            # Update antenna height display
            if hasattr(self, 'antenna_height_input'):
                # Get the current value
                current_value = self.antenna_height_input.value()
                
                # Update the unit label with detected units from CSV
                if hasattr(self, 'antenna_height_unit_label'):
                    self.antenna_height_unit_label.setText(self.antenna_height_units)
                
                # Log the update
                logger.info(f"Updated antenna height from CSV to {current_value}{self.antenna_height_units}")
                
        except Exception as e:
            logger.error(f"Error updating base position info: {str(e)}")
            logger.error(traceback.format_exc())

    def process_csv_files(self):
        """Process all CSV files in the project directory"""
        self.statusBar().showMessage("Processing CSV files...")
        
        all_data = []
        total_files = len(self.detected_files)
        
        for i, csv_file in enumerate(self.detected_files):
            try:
                # Read CSV file
                df = pd.read_csv(csv_file)
                
                # Validate required columns
                required_cols = ['Name', 'Easting', 'Northing', 'Elevation']
                if not all(col in df.columns for col in required_cols):
                    raise ValueError(f"Missing required columns in {os.path.basename(csv_file)}")
                
                # Create processed dataframe with required columns
                processed_df = pd.DataFrame({
                    'Point_name': df['Name'],
                    'Easting': df['Easting'],
                    'Northing': df['Northing'],
                    'Elevation': df['Elevation']  # Use Elevation instead of Ellipsoidal height
                })
                
                all_data.append(processed_df)
                
                # Update status
                self.statusBar().showMessage(f"Processing file {i+1} of {total_files}: {os.path.basename(csv_file)}")
                
            except Exception as e:
                QMessageBox.warning(
                    self,
                    "Processing Warning",
                    f"Error processing {os.path.basename(csv_file)}: {str(e)}"
                )
        
        # Combine all processed data
        if all_data:
            self.processed_data = pd.concat(all_data, ignore_index=True)
            self.statusBar().showMessage("CSV files processed successfully")
        else:
            raise ValueError("No data could be processed")

    def export_csv(self):
        """Export data to CSV based on selected configuration"""
        try:
            # Get output directory
            output_dir = os.path.join(self.project_dir, "processed_output")
            os.makedirs(output_dir, exist_ok=True)
            
            # Process each CSV file
            processed_files = []
            for file in os.listdir(self.project_dir):
                if file.endswith('.csv') and not file.startswith('processed_'):
                    input_file = os.path.join(self.project_dir, file)
                    df = pd.read_csv(input_file)
                    
                    # Create export DataFrame with just the required columns
                    export_df = pd.DataFrame()
                    
                    # Get coordinate system selection
                    is_global = self.coord_sys_toggle.currentText() == "Global (WGS84)"
                    
                    if is_global:
                        # Global coordinate system (WGS84)
                        # Get height unit selection for output
                        output_height_unit = "m" if self.global_height_combo.currentText() == "meters" else "ft"
                        
                        # Copy name
                        export_df['Name'] = df['Name']
                        
                        # Get column order selection
                        is_longitude_first = "Name, Longitude" in self.col_order_toggle.currentText()
                        
                        # Add coordinates in selected order
                        if is_longitude_first:
                            # Longitude first order
                            export_df['Longitude'] = df['Longitude']
                            export_df['Latitude'] = df['Latitude']
                        else:
                            # Latitude first order
                            export_df['Latitude'] = df['Latitude']
                            export_df['Longitude'] = df['Longitude']
                        
                        # Handle height with unit conversion
                        if 'Ellipsoidal height' in df.columns:
                            height_col = 'Ellipsoidal height'
                        else:
                            height_col = 'Elevation'  # Fallback to elevation if ellipsoidal height not present
                        
                        # Get the input height value
                        height_values = df[height_col].copy()
                        
                        # Determine input units based on coordinate system
                        input_height_unit = 'ft' if self.is_feet_based else 'm'
                        logger.info(f"Input height unit: {input_height_unit}, Output height unit: {output_height_unit}")
                        
                        # Convert if units are different
                        if input_height_unit != output_height_unit:
                            if input_height_unit == 'ft' and output_height_unit == 'm':
                                # Convert from US survey feet to meters
                                height_values = height_values / 3.28083333333333
                                logger.info("Converting height from US survey feet to meters")
                            elif input_height_unit == 'm' and output_height_unit == 'ft':
                                # Convert from meters to US survey feet
                                height_values = height_values * 3.28083333333333
                                logger.info("Converting height from meters to US survey feet")
                        
                        # Add to export DataFrame with unit label
                        export_df[f'Ellipsoidal Height ({output_height_unit})'] = height_values
                        
                    else:
                        # Local coordinate system
                        # Get column order selection
                        is_northing_first = "Name, Northing" in self.col_order_toggle.currentText()
                        
                        # Copy name
                        export_df['Name'] = df['Name']
                        
                        # Add coordinates in selected order
                        if is_northing_first:
                            # Northing first order
                            export_df['Northing'] = df['Northing']
                            export_df['Easting'] = df['Easting']
                        else:
                            # Easting first order
                            export_df['Easting'] = df['Easting']
                            export_df['Northing'] = df['Northing']
                        
                        export_df['Elevation'] = df['Elevation']
                    
                    # Generate output filename
                    base_name = os.path.splitext(file)[0]
                    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                    output_file = os.path.join(
                        output_dir,
                        f"{base_name}_processed_{timestamp}.csv"
                    )
                    
                    # Export to CSV
                    export_df.to_csv(output_file, index=False)
                    processed_files.append(output_file)
            
            if processed_files:
                self.statusBar().showMessage(f"Successfully exported {len(processed_files)} files")
                QMessageBox.information(
                    self,
                    "Export Successful",
                    f"Exported {len(processed_files)} files to:\n{output_dir}"
                )
                # Open output directory
                os.startfile(output_dir) if os.name == 'nt' else os.system(f'xdg-open "{output_dir}"')
            else:
                raise ValueError("No files were processed")
            
        except Exception as e:
            logger.error(f"Export error: {str(e)}")
            self.statusBar().showMessage(f"Error during export: {str(e)}")
            QMessageBox.critical(
                self,
                "Export Error",
                f"Failed to export data: {str(e)}"
            )

    def process_position_data(self, rinex_file):
        """Process position data from CSV files"""
        try:
            # Find all CSV files
            csv_files = []
            for file in os.listdir(self.project_dir):
                if file.endswith('.csv') and not file.startswith('processed_'):
                    csv_files.append(os.path.join(self.project_dir, file))
            
            if not csv_files:
                raise ValueError("No CSV files found in project directory")
            
            # Process each CSV file
            all_data = []
            for csv_file in csv_files:
                df = pd.read_csv(csv_file)
                
                # Get coordinate system selection
                is_global = self.coord_sys_toggle.currentText() == "Global (WGS84)"
                
                if is_global:
                    # Global coordinate system (WGS84)
                    # Get height unit selection for output
                    output_height_unit = "m" if self.global_height_combo.currentText() == "meters" else "ft"
                    
                    # Copy name
                    df['Name'] = df['Name']
                    
                    # Get column order selection
                    is_longitude_first = "Name, Longitude" in self.col_order_toggle.currentText()
                    
                    # Add coordinates in selected order
                    if is_longitude_first:
                        # Longitude first order
                        df['Longitude'] = df['Longitude']
                        df['Latitude'] = df['Latitude']
                    else:
                        # Latitude first order
                        df['Latitude'] = df['Latitude']
                        df['Longitude'] = df['Longitude']
                    
                    # Handle height with unit conversion
                    if 'Ellipsoidal height' in df.columns:
                        height_col = 'Ellipsoidal height'
                    else:
                        height_col = 'Elevation'  # Fallback to elevation if ellipsoidal height not present
                    
                    # Get the input height value
                    height_values = df[height_col].copy()
                    
                    # Determine input units based on coordinate system
                    input_height_unit = 'ft' if self.is_feet_based else 'm'
                    logger.info(f"Input height unit: {input_height_unit}, Output height unit: {output_height_unit}")
                    
                    # Convert if units are different
                    if input_height_unit != output_height_unit:
                        if input_height_unit == 'ft' and output_height_unit == 'm':
                            # Convert from US survey feet to meters
                            height_values = height_values / 3.28083333333333
                            logger.info("Converting height from US survey feet to meters")
                        elif input_height_unit == 'm' and output_height_unit == 'ft':
                            # Convert from meters to US survey feet
                            height_values = height_values * 3.28083333333333
                            logger.info("Converting height from meters to US survey feet")
                    
                    # Add to DataFrame with unit label
                    df[f'Ellipsoidal Height ({output_height_unit})'] = height_values
                    
                else:
                    # Local coordinate system
                    # Get column order selection
                    is_northing_first = "Name, Northing" in self.col_order_toggle.currentText()
                    
                    # Copy name
                    df['Name'] = df['Name']
                    
                    # Add coordinates in selected order
                    if is_northing_first:
                        # Northing first order
                        df['Northing'] = df['Northing']
                        df['Easting'] = df['Easting']
                    else:
                        # Easting first order
                        df['Easting'] = df['Easting']
                        df['Northing'] = df['Northing']
                    
                    df['Elevation'] = df['Elevation']
                
                all_data.append(df)
            
            # Combine all data
            if all_data:
                combined_data = pd.concat(all_data, ignore_index=True)
                return combined_data
            else:
                return None
            
        except Exception as e:
            logger.error(f"Error processing position data: {str(e)}")
            logger.error(traceback.format_exc())
            return None

    def find_closest_base_point(self):
        """Find the closest base point to any RINEX file in the project directory."""
        try:
            if not hasattr(self, 'base_points_df') or self.base_points_df is None:
                logger.warning("No base points loaded")
                return None
                
            # Get the RINEX file path from the input field
            rinex_path = self.rinex_input.text()
            if not rinex_path or not os.path.exists(rinex_path):
                logger.warning(f"RINEX file not found: {rinex_path}")
                return None
                
            logger.info(f"Reading RINEX header from: {rinex_path}")
            
            # Get current position from RINEX header
            header = gr.rinexheader(rinex_path)
            current_pos = None
            
            if isinstance(header, dict):
                current_pos = header.get('position', [0, 0, 0])
            else:
                # Try to parse position from header string
                pos_match = re.search(r'APPROX POSITION XYZ\s+([-\d.]+)\s+([-\d.]+)\s+([-\d.]+)', str(header))
                if pos_match:
                    current_pos = [float(pos_match.group(1)), float(pos_match.group(2)), float(pos_match.group(3))]
            
            if not current_pos or len(current_pos) < 3:
                logger.warning("Could not get position from RINEX header")
                return None
                
            logger.info(f"RINEX position (XYZ): {current_pos}")
            
            # Convert current ECEF to lat/lon/height
            transformer = pyproj.Transformer.from_crs('EPSG:4978', 'EPSG:4326', always_xy=True)
            current_lon, current_lat, current_height = transformer.transform(
                current_pos[0], current_pos[1], current_pos[2]
            )
            
            logger.info(f"RINEX position (Lat/Lon): {current_lat}, {current_lon}")
            
            # Calculate distance to each point
            closest_point = None
            min_distance = float('inf')
            
            for idx, point in self.base_points_df.iterrows():
                if 'Latitude' in point and 'Longitude' in point:
                    try:
                        point_lat = float(point['Latitude'])
                        point_lon = float(point['Longitude'])
                        
                        distance = haversine(point_lon, point_lat, current_lon, current_lat)
                        logger.debug(f"Distance to point {point['Name']}: {distance:.2f}m")
                        
                        if distance < min_distance:
                            min_distance = distance
                            closest_point = point
                            
                    except (ValueError, TypeError) as e:
                        logger.warning(f"Could not process point {point['Name']}: {str(e)}")
                        continue
            
            if closest_point is not None:
                logger.info(f"Found closest point: {closest_point['Name']} at {min_distance:.2f}m")
                
                # Create and style the message box
                msg = QMessageBox()
                msg.setIcon(QMessageBox.Question)
                msg.setStandardButtons(QMessageBox.Yes | QMessageBox.No)
                
                # Set the window title and text
                msg.setWindowTitle("Base Station Detection")
                msg.setText(f"<h3 style='color: #4CAF50;'>Found closest base point: {closest_point['Name']}</h3>")
                msg.setInformativeText(f"<p style='color: white;'>Distance: {min_distance:.2f}m</p><p style='color: white;'>Would you like to use this as your base station?</p>")
                
                # Style the message box
                msg.setStyleSheet("""
                    QMessageBox {
                        background-color: #2b2b2b;
                    }
                    QMessageBox QLabel {
                        color: white;
                    }
                    QPushButton {
                        background-color: #424242;
                        color: white;
                        border: 1px solid #555555;
                        padding: 5px 15px;
                        border-radius: 3px;
                        min-width: 80px;
                    }
                    QPushButton:hover {
                        background-color: #4CAF50;
                        border: 1px solid #4CAF50;
                    }
                    QPushButton:pressed {
                        background-color: #45a049;
                    }
                """)
                
                # Get the Yes and No buttons to set their text
                yes_button = msg.button(QMessageBox.Yes)
                no_button = msg.button(QMessageBox.No)
                if yes_button:
                    yes_button.setText("Yes")
                if no_button:
                    no_button.setText("No")
                
                result = msg.exec_()
                logger.info(f"User response: {'Yes' if result == QMessageBox.Yes else 'No'}")
                
                if result == QMessageBox.Yes:
                    # Find and select this point in the combo box
                    index = self.base_point_combo.findText(closest_point['Name'])
                    if index >= 0:
                        self.base_point_combo.setCurrentIndex(index)
                        # This will trigger on_base_point_changed
                        logger.info(f"Selected point {closest_point['Name']} in combo box")
                    
            return closest_point
                
        except Exception as e:
            logger.error(f"Error finding closest base point: {str(e)}")
            logger.error(traceback.format_exc())
            return None

def get_utc_exposure_time_exiftool(image_path):
    """Extract UTC time from DJI image using exiftool."""
    try:
        # Run exiftool to get UTC At Exposure time
        result = subprocess.run(['exiftool', '-UTCAtExposure', '-n', image_path], 
                              capture_output=True, text=True)
        
        if result.returncode == 0:
            # Parse the output to get the UTC time
            for line in result.stdout.split('\n'):
                if 'UTC At Exposure' in line:
                    # Extract the timestamp part
                    timestamp_str = line.split(': ')[1].strip()
                    logger.debug(f"Raw timestamp from exiftool: {timestamp_str}")
                    try:
                        # Try parsing with microseconds
                        utc_time = datetime.strptime(timestamp_str, '%Y:%m:%d %H:%M:%S.%f')
                    except ValueError:
                        # Try without microseconds
                        utc_time = datetime.strptime(timestamp_str, '%Y:%m:%d %H:%M:%S')
                    logger.debug(f"Parsed UTC time: {utc_time}")
                    return utc_time
        return None
    except Exception as e:
        logger.error(f"Error using exiftool: {e}")
        logger.error(traceback.format_exc())
        return None

def get_utc_exposure_time(image_path):
    """Extract UTC time from DJI image using multiple methods."""
    # Try exiftool first (most reliable)
    utc_time = get_utc_exposure_time_exiftool(image_path)
    if utc_time is not None:
        return utc_time
        
    # Try PIL/Pillow
    try:
        with Image.open(image_path) as img:
            exif = img._getexif()
            if exif:
                for tag_id in exif:
                    tag = ExifTags.TAGS.get(tag_id, tag_id)
                    if tag == 'DateTimeOriginal':
                        # Convert to datetime object
                        dt = datetime.strptime(exif[tag_id], '%Y:%m:%d %H:%M:%S')
                        logger.debug(f"PIL timestamp: {dt}")
                        return dt
    except Exception as e:
        logger.error(f"Error using PIL: {e}")
        
    # Try piexif
    try:
        exif_dict = piexif.load(image_path)
        if 'Exif' in exif_dict and piexif.ExifIFD.DateTimeOriginal in exif_dict['Exif']:
            dt_str = exif_dict['Exif'][piexif.ExifIFD.DateTimeOriginal].decode('utf-8')
            dt = datetime.strptime(dt_str, '%Y:%m:%d %H:%M:%S')
            logger.debug(f"piexif timestamp: {dt}")
            return dt
    except Exception as e:
        logger.error(f"Error using piexif: {e}")
        
    # Fallback to filename parsing with 8-hour offset
    try:
        filename = os.path.basename(image_path)
        # Extract timestamp from filename (format: DJI_YYYYMMDDHHMMSS_XXXX_D.JPG)
        timestamp_str = filename.split('_')[1]
        dt = datetime.strptime(timestamp_str, '%Y%m%d%H%M%S')
        # Subtract 8 hours to convert from UTC+8 to UTC
        dt = dt - timedelta(hours=8)
        logger.debug(f"Filename timestamp: {dt}")
        return dt
    except Exception as e:
        logger.error(f"Error parsing filename: {e}")
        return None

def meters_to_us_survey_feet(meters):
    """Convert meters to US survey feet"""
    return meters * 3.28083333333333

def format_shift_display(horizontal_shift_m, vertical_shift_m):
    """Format position shift for display with both meters and US survey feet"""
    # Convert to feet
    horizontal_shift_ft = horizontal_shift_m * 3.28083333333333
    vertical_shift_ft = vertical_shift_m * 3.28083333333333
    
    # Calculate total shift
    total_shift_m = ((horizontal_shift_m ** 2) + (vertical_shift_m ** 2)) ** 0.5
    total_shift_ft = total_shift_m * 3.28083333333333
    
    # Format with appropriate units
    h_display = f"H: {horizontal_shift_m:.3f}m ({horizontal_shift_ft:.3f}ft)"
    v_display = f"V: {vertical_shift_m:.3f}m ({vertical_shift_ft:.3f}ft)"
    total_display = f"Total: {total_shift_m:.3f}m ({total_shift_ft:.3f}ft)"
    
    return f"{total_display}, {h_display}, {v_display}"

def haversine(lon1, lat1, lon2, lat2):
    """Calculate the great circle distance between two points on Earth.
    
    Args:
        lon1, lat1, lon2, lat2: Longitude and latitude in decimal degrees
        
    Returns:
        float: Distance in meters between the points
    """
    # Convert decimal degrees to radians
    lon1, lat1, lon2, lat2 = map(radians, [lon1, lat1, lon2, lat2])
    
    # Haversine formula
    dlon = lon2 - lon1
    dlat = lat2 - lat1
    a = sin(dlat/2)**2 + cos(lat1) * cos(lat2) * sin(dlon/2)**2
    c = 2 * asin(sqrt(a))
    
    # Radius of Earth in meters
    r = 6371000
    
    return c * r

def feet_to_meters(feet):
    """Convert feet to meters."""
    return feet * 0.3048

def convert_to_ecef(lat, lon, height_meters):
    """Convert lat/lon/height to ECEF coordinates."""
    transformer = pyproj.Transformer.from_crs(
        "epsg:4326",  # WGS84 lat/lon
        "epsg:4978",  # ECEF
        always_xy=True
    )
    x, y, z = transformer.transform(lon, lat, height_meters)
    return x, y, z

def update_rinex_header(input_file, output_file, x, y, z):
    """Update RINEX header with new coordinates and zero antenna height."""
    with open(input_file, 'r') as infile, open(output_file, 'w') as outfile:
        in_header = True
        for line in infile:
            if in_header:
                if "APPROX POSITION XYZ" in line:
                    # Format coordinates with exact spacing and decimal places
                    new_line = f"{x:14.4f}{y:14.4f}{z:14.4f}                  APPROX POSITION XYZ \n"
                    outfile.write(new_line)
                elif "ANTENNA: DELTA H/E/N" in line:
                    # Reset antenna height to zero while maintaining format
                    outfile.write("        0.0000        0.0000        0.0000                  ANTENNA: DELTA H/E/N\n")
                elif "END OF HEADER" in line:
                    outfile.write(line)
                    in_header = False
                else:
                    outfile.write(line)
            else:
                outfile.write(line)

if __name__ == '__main__':
    try:
        logger.info("Starting Base Point Correction Tool application")
        app = QApplication(sys.argv)
        app.setStyle('Fusion')  # Use Fusion style for better dark theme support
        window = DJIPPKPro()
        window.show()
        exit_code = app.exec_()
        logger.info(f"Application exit with code: {exit_code}")
        sys.exit(exit_code)
    except Exception as e:
        logger.critical(f"Unhandled exception: {str(e)}")
        logger.critical(traceback.format_exc())
        raise 