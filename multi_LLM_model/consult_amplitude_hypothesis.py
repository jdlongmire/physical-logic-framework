#!/usr/bin/env python3
"""
Multi-LLM Consultation: Amplitude Hypothesis Research

Consults Grok-3, GPT-4, and Gemini-2.0 on approaches to prove the amplitude hypothesis.
"""

import asyncio
import json
import os
import sys
from datetime import datetime
from pathlib import Path

# Add parent directory to path for imports
sys.path.append(str(Path(__file__).parent))

try:
    from claude_llm_bridge import MultiLLMBridge
except ImportError:
    print("Error: claude_llm_bridge.py not found. Make sure you're in the multi_LLM_model directory.")
    sys.exit(1)


def load_research_query():
    """Load the amplitude hypothesis research query"""
    query_file = Path(__file__).parent / "amplitude_hypothesis_research.md"
    if not query_file.exists():
        raise FileNotFoundError(f"Research query file not found: {query_file}")

    with open(query_file, 'r', encoding='utf-8') as f:
        return f.read()


async def consult_on_amplitude_hypothesis():
    """Run multi-LLM consultation on amplitude hypothesis"""

    print("=" * 80)
    print("AMPLITUDE HYPOTHESIS RESEARCH - MULTI-LLM CONSULTATION")
    print("=" * 80)
    print()

    # Load research query
    try:
        query = load_research_query()
        print(f"Loaded research query ({len(query)} characters)")
    except FileNotFoundError as e:
        print(f"Error: {e}")
        return

    # Check API configuration
    config_file = Path(__file__).parent / "api_config.json"
    if not config_file.exists():
        print()
        print("ERROR: API configuration not found!")
        print()
        print("To use this script:")
        print("1. Copy api_config_template.json to api_config.json")
        print("2. Add your API keys for Grok, ChatGPT, and Gemini")
        print("3. Run this script again")
        print()
        print("Alternatively, you can paste the research query from:")
        print(f"  {Path(__file__).parent / 'amplitude_hypothesis_research.md'}")
        print()
        print("Into ChatGPT, Claude, or other LLM interfaces manually.")
        return

    # Initialize bridge
    bridge = MultiLLMBridge()

    print()
    print("Consulting expert LLMs (this may take 30-60 seconds)...")
    print()

    # Run consultation
    try:
        responses = await bridge.consult_all_experts(
            prompt=query,
            max_tokens=8000,  # Long response needed
            temperature=0.3   # Some creativity allowed
        )

        # Save individual responses
        output_dir = Path(__file__).parent / "consultation_results"
        output_dir.mkdir(exist_ok=True)

        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

        for model, response in responses.items():
            filename = output_dir / f"amplitude_hypothesis_{model}_{timestamp}.md"
            with open(filename, 'w', encoding='utf-8') as f:
                f.write(f"# Amplitude Hypothesis Research - {model.upper()}\n\n")
                f.write(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
                f.write("---\n\n")
                f.write(response)

            print(f"✓ Saved {model} response: {filename}")

        # Synthesize responses
        print()
        print("Synthesizing expert responses...")
        synthesis = bridge.synthesize_responses(responses)

        # Save synthesis
        synthesis_file = output_dir / f"amplitude_hypothesis_synthesis_{timestamp}.md"
        with open(synthesis_file, 'w', encoding='utf-8') as f:
            f.write("# Amplitude Hypothesis Research - Multi-LLM Synthesis\n\n")
            f.write(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
            f.write("---\n\n")
            f.write(synthesis)

        print(f"✓ Saved synthesis: {synthesis_file}")

        # Print summary
        print()
        print("=" * 80)
        print("CONSULTATION COMPLETE")
        print("=" * 80)
        print()
        print(f"Results saved to: {output_dir}")
        print()
        print("Next steps:")
        print("1. Review individual expert responses")
        print("2. Read synthesis for consensus recommendations")
        print("3. Prioritize most promising research direction")
        print("4. Begin literature review of recommended papers")

    except Exception as e:
        print(f"Error during consultation: {e}")
        print()
        print("You can still use the research query manually:")
        print(f"  {Path(__file__).parent / 'amplitude_hypothesis_research.md'}")


def main():
    """Main entry point"""
    asyncio.run(consult_on_amplitude_hypothesis())


if __name__ == "__main__":
    main()
