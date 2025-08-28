#!/usr/bin/env python3
"""
Test script for AutoLEAN system
This script tests the basic functionality without requiring a full API key.
"""

import os
import sys
from auto_lean import AutoLEAN

def test_basic_functionality():
    """Test basic functionality without API calls."""
    print("🧪 Testing AutoLEAN Basic Functionality")
    print("=" * 50)

    # Test with a dummy API key
    test_api_key = "test_key_123"

    try:
        # Initialize AutoLEAN
        auto_lean = AutoLEAN(test_api_key)
        print("✅ AutoLEAN class initialized successfully")

        # Test file operations
        test_code = '-- Test Lean4 code\nimport Mathlib.Data.Real.Basic\n\n# Test theorem\ntheorem test : 1 + 1 = 2 := by norm_num'
        auto_lean.save_lean_code(test_code)

        if os.path.exists(auto_lean.solution_file):
            print("✅ Lean4 code file created successfully")

            # Read back the file
            with open(auto_lean.solution_file, 'r', encoding='utf-8') as f:
                content = f.read()
                if content == test_code:
                    print("✅ File content matches expected content")
                else:
                    print("❌ File content mismatch")
        else:
            print("❌ Lean4 code file not created")

        # Test CSV loading (if TestExample.csv exists)
        if os.path.exists("TestExample.csv"):
            try:
                problems = auto_lean.load_problems("TestExample.csv")
                print(f"✅ CSV file loaded successfully with {len(problems)} problems")

                if problems:
                    first_problem = problems[0]
                    print(f"   First problem ID: {first_problem['id']}")
                    print(f"   Problem length: {len(first_problem['problem'])} characters")
                    print(f"   Solution length: {len(first_problem['solution'])} characters")
            except Exception as e:
                print(f"❌ Error loading CSV: {e}")
        else:
            print("⚠️  TestExample.csv not found, skipping CSV test")

        # Clean up test file
        if os.path.exists(auto_lean.solution_file):
            os.remove(auto_lean.solution_file)
            print("✅ Test file cleaned up")

        print("\n🎉 Basic functionality tests completed successfully!")
        return True

    except Exception as e:
        print(f"❌ Test failed with error: {e}")
        return False

def test_environment():
    """Test if the required environment is set up."""
    print("\n🔍 Testing Environment Setup")
    print("=" * 50)

    # Check Python version
    python_version = sys.version_info
    print(f"Python version: {python_version.major}.{python_version.minor}.{python_version.micro}")

    if python_version >= (3, 8):
        print("✅ Python version is compatible")
    else:
        print("❌ Python version too old (need 3.8+)")
        return False

    # Check if required packages can be imported
    try:
        import csv
        print("✅ CSV module available")
    except ImportError:
        print("❌ CSV module not available")
        return False

    try:
        import subprocess
        print("✅ Subprocess module available")
    except ImportError:
        print("❌ Subprocess module not available")
        return False

    # Check if Lean4 is available
    try:
        result = subprocess.run(["lake", "--version"], capture_output=True, text=True, timeout=10)
        if result.returncode == 0:
            print("✅ Lake build system available")
            print(f"   Version: {result.stdout.strip()}")
        else:
            print("⚠️  Lake command failed")
    except (subprocess.TimeoutExpired, FileNotFoundError):
        print("⚠️  Lake command not found or timed out")

    # Check if google-genai is available
    try:
        import google.genai
        print("✅ Google GenAI package available")
    except ImportError:
        print("⚠️  Google GenAI package not installed")
        print("   Run: pip install -r requirements.txt")

    print("\n✅ Environment tests completed!")
    return True

def main():
    """Main test function."""
    print("🚀 AutoLEAN System Test Suite")
    print("=" * 60)

    # Test environment first
    if not test_environment():
        print("\n❌ Environment tests failed. Please fix issues before proceeding.")
        return

    # Test basic functionality
    if not test_basic_functionality():
        print("\n❌ Basic functionality tests failed.")
        return

    print("\n🎉 All tests passed! The AutoLEAN system is ready to use.")
    print("\nNext steps:")
    print("1. Get your Gemini API key from https://makersuite.google.com/app/apikey")
    print("2. Set the GEMINI_API_KEY environment variable")
    print("3. Run: python auto_lean.py")

if __name__ == "__main__":
    main()
