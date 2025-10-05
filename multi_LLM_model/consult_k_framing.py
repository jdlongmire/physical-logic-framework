#!/usr/bin/env python3
"""
Multi-LLM Consultation: K(N)=N-2 Framing Question

Consults Grok-3, GPT-4, and Gemini-2.0 on whether K(N)=N-2 should be framed as
a "fundamental discovery" or "empirical pattern" for publication.

With N=6 validation complete, we now have strong empirical evidence (4/4 test cases)
combined with 5 refuted derivation attempts. Expert input will guide publication strategy.
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


def load_framing_query():
    """Load the K(N) framing query"""
    query_file = Path(__file__).parent / "k_constant_framing_query.md"
    if not query_file.exists():
        raise FileNotFoundError(f"Framing query file not found: {query_file}")

    with open(query_file, 'r', encoding='utf-8') as f:
        return f.read()


async def consult_on_k_framing():
    """Run multi-LLM consultation on K(N) framing question"""

    print("=" * 80)
    print("K(N)=N-2 FRAMING QUESTION - MULTI-LLM EXPERT CONSULTATION")
    print("=" * 80)
    print()
    print("CONTEXT: N=6 validation COMPLETE (|V_4| = 98, pattern HOLDS)")
    print("         5 geometric derivation hypotheses REFUTED")
    print("         Evidence: 4/4 test cases confirmed, 0/5 derivations found")
    print()
    print("QUESTION: Is K(N)=N-2 'fundamental discovery' or 'empirical pattern'?")
    print()

    # Load framing query
    try:
        query = load_framing_query()
        print(f"Loaded framing query ({len(query)} characters)")
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
        print("Alternatively, you can paste the framing query from:")
        print(f"  {Path(__file__).parent / 'k_constant_framing_query.md'}")
        print()
        print("Into ChatGPT, Claude, or other LLM interfaces manually.")
        return

    # Initialize bridge
    bridge = MultiLLMBridge()

    print()
    print("Consulting expert LLMs (this may take 60-90 seconds)...")
    print()

    # Run consultation
    try:
        responses = await bridge.consult_all_experts(
            prompt=query,
            max_tokens=8000,  # Comprehensive response needed
            temperature=0.2   # Conservative, analytical approach
        )

        # Save individual responses
        output_dir = Path(__file__).parent / "consultation_results"
        output_dir.mkdir(exist_ok=True)

        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

        for model, response in responses.items():
            filename = output_dir / f"k_framing_{model}_{timestamp}.md"
            with open(filename, 'w', encoding='utf-8') as f:
                f.write(f"# K(N)=N-2 Framing Question - {model.upper()}\n\n")
                f.write(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
                f.write(f"**Context**: N=6 validation complete, 5 derivation hypotheses refuted\n\n")
                f.write("---\n\n")
                f.write(response)

            print(f"✓ Saved {model} response: {filename}")

        # Synthesize responses
        print()
        print("Synthesizing expert recommendations...")
        synthesis = bridge.synthesize_responses(responses)

        # Save synthesis
        synthesis_file = output_dir / f"k_framing_synthesis_{timestamp}.md"
        with open(synthesis_file, 'w', encoding='utf-8') as f:
            f.write("# K(N)=N-2 Framing Question - Multi-LLM Synthesis\n\n")
            f.write(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
            f.write("**Evidence Summary**:\n")
            f.write("- N=3,4,5,6 validation: 4/4 test cases (100% success)\n")
            f.write("- Derivation attempts: 0/5 hypotheses validated (100% refutation)\n")
            f.write("- Pattern: K = N-2 (simple, elegant formula)\n\n")
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
        print("1. Review individual expert opinions on framing")
        print("2. Read synthesis for consensus recommendation")
        print("3. Choose framing approach based on expert input:")
        print("   - (A) Fundamental discovery (emphasize irreducibility)")
        print("   - (B) Empirical pattern (honest about limitations)")
        print("   - (C) Middle ground (nuanced framing)")
        print("4. Update paper with chosen framing")
        print("5. Prepare for submission to Foundations of Physics")
        print()
        print("Timeline:")
        print("- Framing decision: Now")
        print("- Paper update: 1-2 weeks")
        print("- Submission: 2-3 weeks")

    except Exception as e:
        print(f"Error during consultation: {e}")
        print()
        print("You can still use the framing query manually:")
        print(f"  {Path(__file__).parent / 'k_constant_framing_query.md'}")


def main():
    """Main entry point"""
    asyncio.run(consult_on_k_framing())


if __name__ == "__main__":
    main()
