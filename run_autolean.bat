@echo off
echo ========================================
echo        AutoLEAN System Launcher
echo ========================================
echo.

REM Check if Python is installed
python --version >nul 2>&1
if errorlevel 1 (
    echo ERROR: Python is not installed or not in PATH
    echo Please install Python 3.8+ and try again
    pause
    exit /b 1
)

REM Check if requirements are installed
echo Checking dependencies...
pip show google-genai >nul 2>&1
if errorlevel 1 (
    echo Installing required packages...
    pip install -r requirements.txt
    if errorlevel 1 (
        echo ERROR: Failed to install required packages
        pause
        exit /b 1
    )
)

echo.
echo Dependencies OK!
echo.
echo Choose an option:
echo 1. Run AutoLEAN (single problem processing)
echo 2. Run Batch Processing
echo 3. Run Tests
echo 4. Exit
echo.

set /p choice="Enter your choice (1-4): "

if "%choice%"=="1" (
    echo.
    echo Starting AutoLEAN...
    python auto_lean.py
) else if "%choice%"=="2" (
    echo.
    echo Starting Batch Processing...
    python batch_process.py
) else if "%choice%"=="3" (
    echo.
    echo Running Tests...
    python test_auto_lean.py
) else if "%choice%"=="4" (
    echo Exiting...
    exit /b 0
) else (
    echo Invalid choice. Exiting...
    exit /b 1
)

echo.
echo Press any key to exit...
pause >nul
