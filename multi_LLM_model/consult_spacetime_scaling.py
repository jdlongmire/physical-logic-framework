#!/usr/bin/env python3
"""
Multi-LLM Consultation: Spacetime Scaling Analysis Review

Consults Grok-3, GPT-4, and Gemini-2.0 on the spacetime scaling analysis
from Session 4.0, requesting expert feedback on:

1. Dimension estimation methodology (correlation dimension vs alternatives)
2. Non-monotonic convergence interpretation (1.00 -> 3.16 -> 2.38 -> 2.69)
3. Continuum limit strategy (computational vs analytical vs hybrid)
4. Symmetry group analysis (why automorphisms are so small)
5. Literature comparison (positioning vs existing approaches)
6. Publication strategy (ready for Paper II or need more validation)

Session 4.0 Status: N=3-6 scaling complete, dimension ~ 3 validated but non-monotonic.
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


def load_spacetime_query():
    """Load the spacetime scaling analysis query"""
    query_file = Path(__file__).parent / "spacetime_scaling_query.md"
    if not query_file.exists():
        raise FileNotFoundError(f"Spacetime query file not found: {query_file}")

    with open(query_file, 'r', encoding='utf-8') as f:
        return f.read()


async def consult_on_spacetime_scaling():
    """Run multi-LLM consultation on spacetime scaling analysis"""

    print("=" * 80)
    print("SPACETIME SCALING ANALYSIS - MULTI-LLM EXPERT CONSULTATION")
    print("=" * 80)
    print()
    print("CONTEXT: Session 4.0 - N=3,4,5,6 scaling analysis COMPLETE")
    print("         Spatial dimension: N=4 (3.16), N=6 (2.69) - approaching 3D")
    print("         Metric signature: 100% validated (all spatial intervals spacelike)")
    print("         Symmetry groups: Discrete Poincare-like (G_N ~ S_N x R) for N>=5")
    print()
    print("QUESTIONS: 6 expert review questions on methodology, interpretation, strategy")
    print()

    # Load spacetime query
    try:
        query = load_spacetime_query()
        print(f"Loaded spacetime scaling query ({len(query)} characters)")
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
        print("Alternatively, you can paste the query from:")
        print(f"  {Path(__file__).parent / 'spacetime_scaling_query.md'}")
        print()
        print("Into ChatGPT, Claude, or other LLM interfaces manually.")
        return

    # Initialize bridge
    bridge = MultiLLMBridge()

    print()
    print("Consulting expert LLMs (this may take 90-120 seconds for comprehensive review)...")
    print()

    # Run consultation
    try:
        responses = await bridge.consult_all_experts(
            prompt=query,
            max_tokens=12000,  # Long, detailed technical review needed
            temperature=0.2    # Conservative, analytical approach
        )

        # Save individual responses
        output_dir = Path(__file__).parent / "consultation_results"
        output_dir.mkdir(exist_ok=True)

        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

        for model, response in responses.items():
            filename = output_dir / f"spacetime_scaling_{model}_{timestamp}.md"
            with open(filename, 'w', encoding='utf-8') as f:
                f.write(f"# Spacetime Scaling Analysis Review - {model.upper()}\n\n")
                f.write(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
                f.write(f"**Context**: Session 4.0 - N=3,4,5,6 scaling complete\n\n")
                f.write("**Key Results**:\n")
                f.write("- N=4 dimension: 3.16 (5% above 3D target)\n")
                f.write("- N=6 dimension: 2.69 (10% below 3D target)\n")
                f.write("- Metric signature: 100% validated (spacelike spatial intervals)\n")
                f.write("- Symmetry: Discrete Poincare-like (G_N ~ S_N x R) for N>=5\n")
                f.write("- Non-monotonic convergence: 1.00 -> 3.16 -> 2.38 -> 2.69\n\n")
                f.write("---\n\n")
                f.write(response)

            print(f"✓ Saved {model} response: {filename}")

        # Synthesize responses
        print()
        print("Synthesizing expert recommendations...")
        synthesis = bridge.synthesize_responses(responses)

        # Save synthesis
        synthesis_file = output_dir / f"spacetime_scaling_synthesis_{timestamp}.md"
        with open(synthesis_file, 'w', encoding='utf-8') as f:
            f.write("# Spacetime Scaling Analysis - Multi-LLM Synthesis\n\n")
            f.write(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
            f.write("**Analysis Summary**:\n")
            f.write("- Dimension scaling: N=3 (1.00), N=4 (3.16), N=5 (2.38), N=6 (2.69)\n")
            f.write("- Metric validation: 100% success (all N)\n")
            f.write("- Symmetry groups: Discrete Poincare (G_N ~ S_N x R) for N>=5\n")
            f.write("- Key concern: Non-monotonic convergence pattern\n\n")
            f.write("**Expert Questions**:\n")
            f.write("1. Methodology: Correlation dimension vs alternatives?\n")
            f.write("2. Non-monotonicity: Finite-size effect or genuine structure?\n")
            f.write("3. Continuum limit: Computational vs analytical strategy?\n")
            f.write("4. Symmetries: Why automorphism groups so small?\n")
            f.write("5. Literature: Comparison to causal sets, constructor theory?\n")
            f.write("6. Publication: Ready for Paper II or need more work?\n\n")
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
        print("1. Review individual expert opinions on each question")
        print("2. Read synthesis for consensus recommendations")
        print("3. Decide on methodology adjustments:")
        print("   - Try alternative dimension estimators?")
        print("   - Extend to N=7,8 for more data?")
        print("   - Start analytical continuum limit analysis?")
        print("4. Determine publication timeline:")
        print("   - (A) Paper II now with preliminary scaling results")
        print("   - (B) Wait for continuum limit completion (6-12 months)")
        print("   - (C) Two-paper strategy (metric+symmetries now, continuum later)")
        print("5. Update research roadmap based on expert feedback")
        print()
        print("Timeline (depending on decision):")
        print("- If publish now (A): Paper II draft in 2-4 weeks")
        print("- If continuum limit (B): N=7-10 tests + analysis (2-3 months)")
        print("- If two papers (C): Paper II.A (2-4 weeks), II.B (6-12 months)")

    except Exception as e:
        print(f"Error during consultation: {e}")
        print()
        print("You can still use the spacetime query manually:")
        print(f"  {Path(__file__).parent / 'spacetime_scaling_query.md'}")


def main():
    """Main entry point"""
    asyncio.run(consult_on_spacetime_scaling())


if __name__ == "__main__":
    main()
