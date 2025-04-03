# Base Point Correction Tool

An experimental tool for preparing DJI LiDAR data to be processed in DJI Terra. This tool helps automate the tedious parts of getting your base station data ready for post-processing.

## What it Does

- Reads base station coordinates from Emlid Flow's "All Columns" CSV export
- Automatically finds and updates RINEX base station position with actual coordinates
- Copies the corrected RINEX file to each DJI mission folder
- Smart features:
  - Automatically detects antenna heights from the CSV
  - Finds the most likely base station point by comparing RINEX position
  - Shows timeline view of your missions vs RINEX coverage

## Requirements

- Emlid Flow CSV export (make sure to use "All Columns" configuration!)
- DJI LiDAR mission folders
- RINEX base station file

## How to Use

1. Export a CSV from Emlid Flow using the "All Columns" configuration
2. Put your RINEX file somewhere in your project folder
3. Run the tool and select your project directory
4. The tool will:
   - Find your RINEX file
   - Detect the closest base station point
   - Show you mission timing vs RINEX coverage
   - Create corrected RINEX files in each DJI folder
   - Export a simplified CSV with just the essential coordinate data

After that, you're ready to process in DJI Terra!