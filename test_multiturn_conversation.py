#!/usr/bin/env python3
"""
Test script for multi-turn conversation functionality in AutoLEAN.
This script tests the chat session management and multi-turn conversations.
"""

import os
from auto_lean import AutoLEAN

def test_multiturn_conversation():
    """Test multi-turn conversation functionality."""
    print("🧪 Testing Multi-turn Conversation Functionality")
    print("=" * 60)

    # Test with a dummy API key (we won't actually call the API)
    test_gemini_key = "test_key_123"

    try:
        # Initialize AutoLEAN with Gemini 2.5 Pro
        auto_lean = AutoLEAN(test_gemini_key, model="gemini-2.5-pro")
        print("✅ AutoLEAN class initialized successfully")

        # Test chat session creation
        print("\n🔍 Testing chat session creation...")
        auto_lean.create_new_chat()
        print("✅ Chat session created successfully")

        # Test sending messages (mock)
        print("\n🔍 Testing message sending...")

        # Mock the send_chat_message method to avoid actual API calls
        def mock_send_message(message):
            return f"Mock response to: {message[:50]}..."

        original_send = auto_lean.send_chat_message
        auto_lean.send_chat_message = mock_send_message

        try:
            # Test first message
            response1 = auto_lean.send_chat_message("Hello, I need help with a math problem.")
            print(f"✅ First message response: {response1}")

            # Test second message (should maintain context)
            response2 = auto_lean.send_chat_message("Can you help me solve it?")
            print(f"✅ Second message response: {response2}")

            # Test third message (should maintain context)
            response3 = auto_lean.send_chat_message("The problem is about calculus.")
            print(f"✅ Third message response: {response3}")

        finally:
            # Restore original method
            auto_lean.send_chat_message = original_send

        # Test chat history
        print("\n🔍 Testing chat history...")
        history = auto_lean.get_chat_history()
        print(f"✅ Chat history retrieved: {len(history)} messages")

        # Test new chat creation (should reset context)
        print("\n🔍 Testing new chat creation...")
        auto_lean.create_new_chat()
        print("✅ New chat session created successfully")

        print("\n🎉 Multi-turn conversation test completed successfully!")
        return True

    except Exception as e:
        print(f"❌ Test failed with error: {e}")
        return False

def test_model_selection():
    """Test model selection functionality."""
    print("\n🤖 Testing Model Selection")
    print("=" * 60)

    test_gemini_key = "test_key_123"

    try:
        # Test Gemini 2.5 Pro
        auto_lean_pro = AutoLEAN(test_gemini_key, model="gemini-2.5-pro")
        print("✅ Gemini 2.5 Pro model initialized successfully")
        print(f"   Model: {auto_lean_pro.gemini_model}")

        # Test Gemini 2.5 Flash
        auto_lean_flash = AutoLEAN(test_gemini_key, model="gemini-2.5-flash")
        print("✅ Gemini 2.5 Flash model initialized successfully")
        print(f"   Model: {auto_lean_flash.gemini_model}")

        # Test default model
        auto_lean_default = AutoLEAN(test_gemini_key)
        print("✅ Default model initialized successfully")
        print(f"   Model: {auto_lean_default.gemini_model}")

        print("\n🎉 Model selection test completed successfully!")
        return True

    except Exception as e:
        print(f"❌ Test failed with error: {e}")
        return False

def test_chat_session_management():
    """Test chat session management for multiple problems."""
    print("\n🔄 Testing Chat Session Management")
    print("=" * 60)

    test_gemini_key = "test_key_123"

    try:
        auto_lean = AutoLEAN(test_gemini_key, model="gemini-2.5-pro")

        # Simulate processing multiple problems
        problems = ["Problem 1", "Problem 2", "Problem 3"]

        for i, problem in enumerate(problems, 1):
            print(f"\n📝 Processing {problem}...")

            # Create new chat for each problem
            auto_lean.create_new_chat()
            print(f"   ✅ Created new chat session for {problem}")

            # Simulate some messages in the chat
            print(f"   📤 Simulating messages for {problem}...")

            # Mock the send_chat_message method
            def mock_send_message(message):
                return f"Response for {problem}: {message[:30]}..."

            original_send = auto_lean.send_chat_message
            auto_lean.send_chat_message = mock_send_message

            try:
                response = auto_lean.send_chat_message(f"Let's solve {problem}")
                print(f"   📥 Response: {response}")
            finally:
                auto_lean.send_chat_message = original_send

        print("\n🎉 Chat session management test completed successfully!")
        return True

    except Exception as e:
        print(f"❌ Test failed with error: {e}")
        return False

def main():
    """Main test function."""
    print("🚀 AutoLEAN Multi-turn Conversation Test Suite")
    print("=" * 80)

    # Run tests
    tests = [
        ("Multi-turn Conversation", test_multiturn_conversation),
        ("Model Selection", test_model_selection),
        ("Chat Session Management", test_chat_session_management),
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
