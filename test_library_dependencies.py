#!/usr/bin/env python3
"""
Test program for Library Dependencies in AutoLEAN
This program tests the library dependency resolution and validation functionality.
"""

import os
import sys
from auto_lean import AutoLEAN

def test_library_dependency_resolution():
    """Test the library dependency resolution functionality."""
    print("🧪 Testing Library Dependency Resolution")
    print("=" * 60)

    # Test with a dummy API key (we won't actually call the API)
    test_gemini_key = "test_key_123"
    test_openrouter_key = "test_key_456"

    try:
        # Initialize AutoLEAN
        auto_lean = AutoLEAN(test_gemini_key, test_openrouter_key)
        print("✅ AutoLEAN class initialized successfully")

        # Test data
        test_solution = """
        We need to prove that for any positive integer n, the sum of the first n natural numbers is n(n+1)/2.
        This can be proven using mathematical induction.
        First, we show the base case for n=1.
        Then we assume the statement holds for n=k and prove it for n=k+1.
        """

        test_part_descriptions = """
        PART 1: Base case - prove for n=1
        PART 2: Inductive step - assume for n=k, prove for n=k+1
        PART 3: Conclusion - by induction, the statement holds for all n
        """

        num_parts = 3

        print(f"\n📝 Test Solution:")
        print(test_solution[:100] + "...")

        print(f"\n📝 Test Part Descriptions:")
        print(test_part_descriptions)

        # Test the resolve_library_dependencies method
        print(f"\n🔍 Testing resolve_library_dependencies method...")

        # Mock the call_gemini method to return test data
        def mock_call_gemini(prompt):
            return """
            Based on the solution, you will need the following imports:

            import Mathlib.Data.Nat.Basic
            import Mathlib.Algebra.BigOperators.Basic
            import Mathlib.Data.Finset.Basic
            import Mathlib.Tactic.Ring
            import Mathlib.Tactic.Linarith
            """

        # Replace the call_gemini method temporarily
        original_call_gemini = auto_lean.call_gemini
        auto_lean.call_gemini = mock_call_gemini

        try:
            library_imports = auto_lean.resolve_library_dependencies(
                test_solution, num_parts, test_part_descriptions
            )

            print("✅ Library dependency resolution completed")
            print(f"\n📋 Generated Library Imports:")
            print(library_imports)

            # Validate the imports
            print(f"\n🔍 Validating generated imports...")
            is_valid, error_message = auto_lean.validate_library_imports(library_imports)

            if is_valid:
                print("✅ Library imports are valid!")
            else:
                print("❌ Library imports validation failed:")
                print(error_message)

        finally:
            # Restore the original method
            auto_lean.call_gemini = original_call_gemini

    except Exception as e:
        print(f"❌ Test failed with error: {e}")
        return False

    return True

def test_import_correction():
    """Test the import correction functionality."""
    print("\n🔧 Testing Import Correction")
    print("=" * 60)

    # Test cases with incorrect imports
    test_cases = [
        {
            "name": "Missing Mathlib prefix",
            "incorrect_imports": """
import Algebra.BigOperators.Group.Finset.Lemmas
import Algebra.Order.Group.Abs
import Data.Fin.Basic
import Data.Finset.Interval
import Data.Int.Cast.Lemmas
import Data.Nat.Ceil
import Data.Rat.Cast
import Logic.Function.Basic
""",
            "expected_prefix": "Mathlib."
        },
        {
            "name": "Mixed correct and incorrect",
            "incorrect_imports": """
import Mathlib.Data.Nat.Basic
import Algebra.BigOperators.Basic
import Mathlib.Tactic.Ring
import Data.Finset.Basic
""",
            "expected_prefix": "Mathlib."
        }
    ]

    for test_case in test_cases:
        print(f"\n📝 Test Case: {test_case['name']}")
        print("Input imports:")
        print(test_case['incorrect_imports'])

        # Correct the imports
        corrected_imports = correct_imports(test_case['incorrect_imports'])

        print("Corrected imports:")
        print(corrected_imports)

        # Validate the correction
        lines = corrected_imports.strip().split('\n')
        all_correct = True

        for line in lines:
            line = line.strip()
            if line.startswith('import ') and 'Mathlib' in line:
                if not line.startswith('import Mathlib.'):
                    print(f"❌ Incorrect import: {line}")
                    all_correct = False

        if all_correct:
            print("✅ All imports corrected successfully!")
        else:
            print("❌ Some imports still need correction")

def correct_imports(import_text: str) -> str:
    """Correct import statements by adding Mathlib prefix where missing."""
    lines = import_text.strip().split('\n')
    corrected_lines = []

    for line in lines:
        line = line.strip()
        if line.startswith('import ') and not line.startswith('import Mathlib.'):
            # Extract the module path after 'import '
            module_path = line[7:]  # Remove 'import '
            # Add Mathlib prefix
            corrected_line = f"import Mathlib.{module_path}"
            corrected_lines.append(corrected_line)
        elif line.startswith('import Mathlib.'):
            # Already correct
            corrected_lines.append(line)
        elif line and not line.startswith('--'):
            # Non-empty line that's not a comment
            corrected_lines.append(line)

    return '\n'.join(corrected_lines)

def test_mathlib_structure_loading():
    """Test loading and parsing of mathlib structure."""
    print("\n📚 Testing Mathlib Structure Loading")
    print("=" * 60)

    try:
        # Test with a dummy API key
        test_gemini_key = "test_key_123"
        auto_lean = AutoLEAN(test_gemini_key)

        print("✅ AutoLEAN initialized successfully")

        # Check if mathlib structure was loaded
        if auto_lean.mathlib_structure:
            print("✅ Mathlib structure loaded successfully")
            print(f"📏 Structure length: {len(auto_lean.mathlib_structure)} characters")

            # Show first few lines
            lines = auto_lean.mathlib_structure.split('\n')[:10]
            print("📋 First 10 lines of structure:")
            for i, line in enumerate(lines, 1):
                print(f"{i:2d}: {line}")

        else:
            print("⚠️  Mathlib structure not loaded or empty")

    except Exception as e:
        print(f"❌ Test failed with error: {e}")

def test_import_validation():
    """Test the import validation functionality."""
    print("\n✅ Testing Import Validation")
    print("=" * 60)

    try:
        # Test with a dummy API key
        test_gemini_key = "test_key_123"
        auto_lean = AutoLEAN(test_gemini_key)

        # Test cases
        test_imports = [
            {
                "name": "Valid basic imports",
                "imports": """
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
""",
                "should_be_valid": True
            },
            {
                "name": "Invalid imports (missing Mathlib)",
                "imports": """
import Data.Nat.Basic
import Algebra.Ring.Basic
""",
                "should_be_valid": False
            }
        ]

        for test_case in test_imports:
            print(f"\n📝 Test Case: {test_case['name']}")
            print("Testing imports:")
            print(test_case['imports'])

            is_valid, error_message = auto_lean.validate_library_imports(test_case['imports'])

            if is_valid == test_case['should_be_valid']:
                print("✅ Validation result matches expectation")
            else:
                print("❌ Validation result doesn't match expectation")
                print(f"Expected: {test_case['should_be_valid']}, Got: {is_valid}")
                if error_message:
                    print(f"Error message: {error_message}")

    except Exception as e:
        print(f"❌ Test failed with error: {e}")

def main():
    """Main test function."""
    print("🚀 AutoLEAN Library Dependencies Test Suite")
    print("=" * 80)

    # Check if mathlib_structure.txt exists
    if not os.path.exists("mathlib_structure.txt"):
        print("⚠️  mathlib_structure.txt not found. Some tests may not work properly.")
        print("   Please ensure the file exists in the current directory.")

    # Run tests
    tests = [
        ("Mathlib Structure Loading", test_mathlib_structure_loading),
        ("Import Correction", test_import_correction),
        ("Import Validation", test_import_validation),
        ("Library Dependency Resolution", test_library_dependency_resolution),
    ]

    results = []

    for test_name, test_func in tests:
        print(f"\n{'='*80}")
        print(f"Running: {test_name}")
        print('='*80)

        try:
            success = test_func()
            results.append((test_name, success))
        except Exception as e:
            print(f"❌ Test '{test_name}' failed with exception: {e}")
            results.append((test_name, False))

    # Summary
    print(f"\n{'='*80}")
    print("📊 TEST SUMMARY")
    print('='*80)

    passed = 0
    total = len(results)

    for test_name, success in results:
        status = "✅ PASSED" if success else "❌ FAILED"
        print(f"{test_name}: {status}")
        if success:
            passed += 1

    print(f"\nOverall: {passed}/{total} tests passed")

    if passed == total:
        print("🎉 All tests passed!")
    else:
        print("⚠️  Some tests failed. Please review the output above.")

if __name__ == "__main__":
    main()
