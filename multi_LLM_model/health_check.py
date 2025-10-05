#!/usr/bin/env python3
"""
Multi-LLM Team Health Check

Quick diagnostic to verify API configuration and team availability.
Run at start of each session to ensure consultation capability is ready.
"""

import json
import os
from pathlib import Path

def health_check():
    """
    Perform multi-LLM team health check

    Checks:
    1. API config file exists
    2. Required API keys present
    3. Config file structure valid
    4. Team members identified

    Returns: Status report (no actual API calls to save quota)
    """

    print("=" * 80)
    print("MULTI-LLM TEAM HEALTH CHECK")
    print("=" * 80)
    print()

    # Check 1: Config file exists
    config_path = Path(__file__).parent / "api_config.json"

    if not config_path.exists():
        print("❌ STATUS: NOT CONFIGURED")
        print()
        print("API configuration file not found.")
        print(f"Expected location: {config_path}")
        print()
        print("To configure:")
        print("1. Copy api_config_template.json to api_config.json")
        print("2. Add API keys for available models")
        print("3. Run health check again")
        print()
        print("CONSULTATION CAPABILITY: OFFLINE")
        print("(Manual query option available via ChatGPT/Claude web interfaces)")
        return False

    # Check 2: Load and validate config
    try:
        with open(config_path, 'r') as f:
            config = json.load(f)
    except json.JSONDecodeError as e:
        print("❌ STATUS: CONFIGURATION ERROR")
        print()
        print(f"Invalid JSON in api_config.json: {e}")
        print("Please fix configuration file and try again.")
        return False

    # Check 3: Identify available team members
    print("✓ Configuration file found and valid")
    print()
    print("TEAM ROSTER:")
    print("-" * 80)

    available = []
    unavailable = []

    # Check for each potential team member
    team_members = {
        "grok_api_key": "Grok-3 (xAI)",
        "openai_api_key": "GPT-4 (OpenAI)",
        "gemini_api_key": "Gemini-2.0-Pro (Google)",
        "anthropic_api_key": "Claude-3.5-Sonnet (Anthropic)"
    }

    for key, name in team_members.items():
        if key in config and config[key] and config[key].strip():
            # Check if it's a placeholder
            if config[key].startswith("your_") or config[key] == "":
                unavailable.append(name)
                print(f"  ⚠️  {name:<30} NOT CONFIGURED (placeholder key)")
            else:
                available.append(name)
                # Don't print actual key, just first 4 chars
                key_preview = config[key][:8] + "..." if len(config[key]) > 8 else "***"
                print(f"  ✓  {name:<30} CONFIGURED ({key_preview})")
        else:
            unavailable.append(name)
            print(f"  ❌ {name:<30} MISSING")

    print()
    print("=" * 80)
    print(f"AVAILABLE EXPERTS: {len(available)}/{len(team_members)}")
    print("=" * 80)

    if len(available) == 0:
        print()
        print("❌ NO EXPERTS CONFIGURED")
        print()
        print("CONSULTATION CAPABILITY: OFFLINE")
        print("Recommendation: Configure at least 2-3 API keys for multi-LLM consultation")
        print()
        print("Alternative: Use manual consultation via web interfaces")
        return False

    elif len(available) == 1:
        print()
        print(f"⚠️  SINGLE EXPERT ONLY: {available[0]}")
        print()
        print("CONSULTATION CAPABILITY: LIMITED")
        print("Recommendation: Configure additional APIs for diverse perspectives")
        print("Benefits of multi-LLM: Cross-validation, blind spot detection, consensus")
        return True

    else:
        print()
        print(f"✓ MULTI-EXPERT TEAM READY ({len(available)} experts)")
        print()
        for expert in available:
            print(f"  • {expert}")
        print()
        print("CONSULTATION CAPABILITY: FULL")
        print("Ready for parallel expert consultation on research questions")
        return True


def main():
    """Run health check and report status"""
    is_ready = health_check()

    print()
    print("-" * 80)
    if is_ready:
        print("READY FOR CONSULTATION ✓")
    else:
        print("CONSULTATION OFFLINE - Manual queries available")
    print("-" * 80)
    print()

    return is_ready


if __name__ == "__main__":
    main()
