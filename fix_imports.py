#!/usr/bin/env python3
"""
Utility script to fix import statements in AutoLEAN generated code.
This script corrects imports that are missing the "Mathlib." prefix.
"""

import re
import os
import sys

def fix_imports_in_text(text: str) -> str:
    """Fix import statements in text by adding Mathlib prefix where missing."""
    lines = text.split('\n')
    fixed_lines = []

    for line in lines:
        # Check if line is an import statement
        if line.strip().startswith('import ') and not line.strip().startswith('import Mathlib.'):
            # Extract the module path after 'import '
            match = re.match(r'^(\s*)import\s+(.+)$', line)
            if match:
                indent = match.group(1)
                module_path = match.group(2).strip()

                # Skip if it's already a Mathlib import or a relative import
                if not module_path.startswith('Mathlib.') and not module_path.startswith('.'):
                    # Add Mathlib prefix
                    fixed_line = f"{indent}import Mathlib.{module_path}"
                    fixed_lines.append(fixed_line)
                    print(f"Fixed: {line.strip()} -> {fixed_line.strip()}")
                else:
                    fixed_lines.append(line)
            else:
                fixed_lines.append(line)
        else:
            fixed_lines.append(line)

    return '\n'.join(fixed_lines)

def fix_file_imports(file_path: str) -> bool:
    """Fix imports in a specific file."""
    if not os.path.exists(file_path):
        print(f"❌ File not found: {file_path}")
        return False

    try:
        # Read the file
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        # Fix imports
        fixed_content = fix_imports_in_text(content)

        # Check if any changes were made
        if fixed_content != content:
            # Write back to file
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(fixed_content)
            print(f"✅ Fixed imports in: {file_path}")
            return True
        else:
            print(f"ℹ️  No import fixes needed in: {file_path}")
            return False

    except Exception as e:
        print(f"❌ Error processing file {file_path}: {e}")
        return False

def fix_directory_imports(directory: str, extensions: list = None) -> int:
    """Fix imports in all files in a directory."""
    if extensions is None:
        extensions = ['.lean', '.py']

    fixed_count = 0

    for root, dirs, files in os.walk(directory):
        for file in files:
            if any(file.endswith(ext) for ext in extensions):
                file_path = os.path.join(root, file)
                if fix_file_imports(file_path):
                    fixed_count += 1

    return fixed_count

def validate_imports_in_text(text: str) -> list:
    """Validate import statements and return list of issues."""
    issues = []
    lines = text.split('\n')

    for line_num, line in enumerate(lines, 1):
        line = line.strip()
        if line.startswith('import ') and not line.startswith('import Mathlib.'):
            # Check if it's a relative import (starts with .)
            if not line.startswith('import .'):
                issues.append({
                    'line': line_num,
                    'content': line,
                    'issue': 'Missing Mathlib prefix'
                })

    return issues

def main():
    """Main function."""
    print("🔧 AutoLEAN Import Fixer")
    print("=" * 50)

    if len(sys.argv) < 2:
        print("Usage:")
        print("  python fix_imports.py <file_or_directory>")
        print("  python fix_imports.py --validate <file>")
        print("  python fix_imports.py --test")
        print()
        print("Examples:")
        print("  python fix_imports.py solutionProcess.lean")
        print("  python fix_imports.py results/")
        print("  python fix_imports.py --validate solutionProcess.lean")
        return

    command = sys.argv[1]

    if command == "--test":
        # Run test cases
        print("🧪 Running test cases...")

        test_cases = [
            {
                "name": "Missing Mathlib prefix",
                "input": """
import Algebra.BigOperators.Group.Finset.Lemmas
import Data.Fin.Basic
import Mathlib.Data.Nat.Basic
""",
                "expected": """
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
"""
            }
        ]

        for test_case in test_cases:
            print(f"\n📝 Test: {test_case['name']}")
            print("Input:")
            print(test_case['input'])

            result = fix_imports_in_text(test_case['input'])
            print("Output:")
            print(result)

            # Check if result matches expected
            if result.strip() == test_case['expected'].strip():
                print("✅ Test passed!")
            else:
                print("❌ Test failed!")
                print("Expected:")
                print(test_case['expected'])

    elif command == "--validate":
        if len(sys.argv) < 3:
            print("❌ Please provide a file to validate")
            return

        file_path = sys.argv[2]
        if not os.path.exists(file_path):
            print(f"❌ File not found: {file_path}")
            return

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()

            issues = validate_imports_in_text(content)

            if issues:
                print(f"❌ Found {len(issues)} import issues in {file_path}:")
                for issue in issues:
                    print(f"  Line {issue['line']}: {issue['content']} ({issue['issue']})")
            else:
                print(f"✅ No import issues found in {file_path}")

        except Exception as e:
            print(f"❌ Error reading file: {e}")

    else:
        # Fix imports in file or directory
        target = command

        if os.path.isfile(target):
            print(f"🔧 Fixing imports in file: {target}")
            if fix_file_imports(target):
                print("✅ File processed successfully")
            else:
                print("ℹ️  No changes needed")

        elif os.path.isdir(target):
            print(f"🔧 Fixing imports in directory: {target}")
            fixed_count = fix_directory_imports(target)
            print(f"✅ Fixed imports in {fixed_count} files")

        else:
            print(f"❌ Target not found: {target}")

if __name__ == "__main__":
    main()
