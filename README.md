# Base Point Correction Tool

A professional tool for processing PPK (Post-Processing Kinematic) data with RINEX base station corrections. This application provides a user-friendly interface for handling coordinate transformations and PPK data processing.

## Features

- Process PPK data using RINEX base station files
- Support for multiple coordinate systems
- Real-time RINEX coverage analysis
- Base station position correction
- Satellite system detection and validation
- Coordinate transformation capabilities
- User-friendly graphical interface
- Timeline visualization for mission planning

## System Requirements

- Windows 10 or later
- Minimum 4GB RAM (8GB recommended)
- 200MB free disk space

## Installation

1. Download the latest release from the [Releases](../../releases) page
2. Extract the ZIP file to your desired location
3. Run `Base_Point_Correction_Tool.exe`

Note: On first run, Windows SmartScreen may show a warning. This is normal for new applications. Click "More Info" and then "Run Anyway" to proceed.

## Usage

1. Select your project directory containing:
   - RINEX base station files
   - DJI flight mission folders
   - CSV coordinate files

2. Choose your base station point from the available points list

3. Configure processing options:
   - Antenna height
   - Coordinate system
   - Output format preferences

4. Process your data or export coordinates

For detailed usage instructions, see the [User Guide](docs/USER_GUIDE.md).

## Building from Source

Requirements:
- Python 3.11 or later
- Required packages listed in requirements.txt

```bash
# Install dependencies
pip install -r requirements.txt

# Run the application
python base_point_correction.py
```

## Security

This application:
- Does not collect any user data
- Processes all data locally on your machine
- Does not require internet connection
- Does not modify original data files

## Support

For issues, questions, or suggestions:
- Open an issue in this repository
- Contact the developer through GitHub

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Acknowledgments

- PyQt5 for the graphical interface
- GeorineX for RINEX file processing
- All contributors and users of this tool 