#!/usr/bin/env python3
"""
Simple test script to demonstrate the import fixing functionality.
"""

def fix_imports_in_text(text: str) -> str:
    """Fix import statements in text by adding Mathlib prefix where missing."""
    lines = text.split('\n')
    fixed_lines = []

    for line in lines:
        line = line.strip()
        if line.startswith('import ') and not line.startswith('import Mathlib.') and not line.startswith('import .'):
            # Add Mathlib prefix
            module_path = line[7:]  # Remove 'import '
            fixed_line = f"import Mathlib.{module_path}"
            fixed_lines.append(fixed_line)
            print(f"Fixed: {line} -> {fixed_line}")
        else:
            fixed_lines.append(line)

    return '\n'.join(fixed_lines)

def main():
    """Test the import fixing functionality."""
    print("🧪 Testing Import Fix Functionality")
    print("=" * 50)

    # Test case with incorrect imports
    test_imports = """
import Algebra.BigOperators.Group.Finset.Lemmas
import Algebra.Order.Group.Abs
import Data.Fin.Basic
import Data.Finset.Interval
import Data.Int.Cast.Lemmas
import Data.Nat.Ceil
import Data.Rat.Cast
import Logic.Function.Basic
"""

    print("📝 Original imports (incorrect):")
    print(test_imports)

    print("\n🔧 Fixing imports...")
    fixed_imports = fix_imports_in_text(test_imports)

    print("\n✅ Fixed imports:")
    print(fixed_imports)

    # Validate the fix
    print("\n🔍 Validation:")
    lines = fixed_imports.strip().split('\n')
    all_correct = True

    for line in lines:
        line = line.strip()
        if line.startswith('import '):
            if not line.startswith('import Mathlib.'):
                print(f"❌ Still incorrect: {line}")
                all_correct = False
            else:
                print(f"✅ Correct: {line}")

    if all_correct:
        print("\n🎉 All imports fixed successfully!")
    else:
        print("\n⚠️  Some imports still need fixing")

if __name__ == "__main__":
    main()
