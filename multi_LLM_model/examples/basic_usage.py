#!/usr/bin/env python3
"""
Basic Usage Example - Multi-LLM Expert Consultation

This example shows the simplest way to use the Multi-LLM system:
1. Query all experts in parallel
2. Get synthesized recommendations
3. View individual responses
"""

import asyncio
import sys
import os

# Add parent directory to path to import the bridge
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from claude_llm_bridge import MultiLLMBridge


async def main():
    """Basic consultation example"""

    # Initialize the bridge (requires api_config.json with your API keys)
    bridge = MultiLLMBridge()

    # Your question or problem
    prompt = """
    What is the best way to implement binary search in Python?
    Please include:
    1. Time complexity analysis
    2. Edge cases to consider
    3. Working code example
    """

    print("Querying all AI experts in parallel...")
    print(f"Question: {prompt.strip()}\n")
    print("=" * 60)

    # Query all experts concurrently (Grok, ChatGPT, Gemini)
    responses = await bridge.consult_all_experts(prompt)

    # Synthesize responses into actionable recommendations
    synthesis = bridge.synthesize_responses(responses)

    # Print synthesis summary
    bridge.print_synthesis_summary(synthesis)

    # Access individual expert responses
    print("\n" + "=" * 60)
    print("INDIVIDUAL EXPERT RESPONSES")
    print("=" * 60)

    for response in responses:
        if response['success']:
            print(f"\n{response['source'].upper()} ({response['model']}):")
            print("-" * 60)
            print(response['content'])
        else:
            print(f"\n{response['source'].upper()}: FAILED")
            print(f"Error: {response.get('error', 'Unknown error')}")

    # Optional: Save detailed log
    log_file = bridge.save_consultation_log({
        'prompt': prompt,
        'responses': responses,
        'synthesis': synthesis
    }, filename='basic_usage_log.json')

    print(f"\n\nDetailed log saved to: {log_file}")


if __name__ == "__main__":
    # Run the async function
    asyncio.run(main())
