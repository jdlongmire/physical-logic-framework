#!/usr/bin/env python3
"""
Proof Validation Consultation - Multi-LLM Expert Review

Consults expert LLMs to validate the amplitude hypothesis proof before proceeding.
CRITICAL: We need to verify logical soundness before claiming breakthrough.
"""

import asyncio
import json
import os
import sys
from datetime import datetime
from pathlib import Path

sys.path.append(str(Path(__file__).parent))

try:
    from claude_llm_bridge import MultiLLMBridge
except ImportError:
    print("Error: claude_llm_bridge.py not found")
    sys.exit(1)


def load_validation_query():
    """Load the proof validation query"""
    query_file = Path(__file__).parent / "proof_validation_query.md"
    if not query_file.exists():
        raise FileNotFoundError(f"Validation query not found: {query_file}")

    with open(query_file, 'r', encoding='utf-8') as f:
        return f.read()


def load_full_proof():
    """Load the complete proof document"""
    proof_file = Path(__file__).parent.parent / "paper" / "supplementary" / "amplitude_hypothesis_proof.md"
    if not proof_file.exists():
        print(f"Warning: Full proof document not found at {proof_file}")
        return None

    with open(proof_file, 'r', encoding='utf-8') as f:
        return f.read()


async def validate_proof():
    """Run multi-LLM proof validation consultation"""

    print("=" * 80)
    print("AMPLITUDE HYPOTHESIS PROOF - EXPERT VALIDATION")
    print("=" * 80)
    print()
    print("CRITICAL: Validating proof logic before proceeding with publication")
    print()

    # Load validation query
    try:
        query = load_validation_query()
        print(f"[OK] Loaded validation query ({len(query)} characters)")
    except FileNotFoundError as e:
        print(f"Error: {e}")
        return

    # Load full proof (optional, for context)
    full_proof = load_full_proof()
    if full_proof:
        print(f"[OK] Loaded full proof document ({len(full_proof)} characters)")

    # Check API configuration
    config_file = Path(__file__).parent / "api_config.json"
    if not config_file.exists():
        print()
        print("=" * 80)
        print("API CONFIGURATION REQUIRED")
        print("=" * 80)
        print()
        print("The multi-LLM consultation requires API keys.")
        print()
        print("OPTION 1: Configure API keys")
        print("  1. Copy api_config_template.json to api_config.json")
        print("  2. Add your API keys for Grok, ChatGPT, and/or Gemini")
        print("  3. Run this script again")
        print()
        print("OPTION 2: Manual validation (RECOMMENDED)")
        print("  The validation query has been prepared at:")
        print(f"    {Path(__file__).parent / 'proof_validation_query.md'}")
        print()
        print("  You can:")
        print("  - Paste it into ChatGPT (GPT-4)")
        print("  - Paste it into Claude (claude.ai)")
        print("  - Paste it into Gemini")
        print("  - Send to expert physicists/mathematicians")
        print()
        print("  Save responses in:")
        print(f"    {Path(__file__).parent / 'validation_results' / ''}")
        print()
        print("=" * 80)
        print()
        print("The validation query is ready for manual submission.")
        print(f"Length: {len(query)} characters (~12KB)")
        print()
        print("Includes:")
        print("- Complete proof chain")
        print("- 6 critical validation questions")
        print("- Specific mathematical concerns")
        print("- Comparison to prior work (Caticha, Jaynes, Zurek)")
        print("- Red flags to check (circularity, assumptions, etc.)")
        print()
        return

    # Initialize bridge
    bridge = MultiLLMBridge()

    print()
    print("Consulting expert LLMs for proof validation...")
    print("(This may take 60-120 seconds due to length and complexity)")
    print()

    # Run consultation
    try:
        responses = await bridge.consult_all_experts(
            prompt=query,
            max_tokens=12000,  # Long detailed response needed
            temperature=0.2    # Low temperature for rigorous analysis
        )

        # Save individual responses
        output_dir = Path(__file__).parent / "validation_results"
        output_dir.mkdir(exist_ok=True)

        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

        for model, response in responses.items():
            filename = output_dir / f"proof_validation_{model}_{timestamp}.md"
            with open(filename, 'w', encoding='utf-8') as f:
                f.write(f"# Proof Validation - {model.upper()}\n\n")
                f.write(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
                f.write("---\n\n")
                f.write(response)

            print(f"[OK] Saved {model} validation: {filename}")

        # Synthesize responses
        print()
        print("Synthesizing expert opinions...")
        synthesis = bridge.synthesize_responses(responses)

        # Save synthesis
        synthesis_file = output_dir / f"proof_validation_synthesis_{timestamp}.md"
        with open(synthesis_file, 'w', encoding='utf-8') as f:
            f.write("# Proof Validation - Multi-Expert Synthesis\n\n")
            f.write(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
            f.write("**Experts Consulted**: " + ", ".join(responses.keys()) + "\n\n")
            f.write("---\n\n")
            f.write(synthesis)

        print(f"[OK] Saved synthesis: {synthesis_file}")

        # Analyze results
        print()
        print("=" * 80)
        print("VALIDATION COMPLETE")
        print("=" * 80)
        print()
        print(f"Expert responses saved to: {output_dir}")
        print()
        print("NEXT STEPS:")
        print()
        print("1. READ the synthesis file carefully")
        print("2. REVIEW individual expert responses")
        print("3. IDENTIFY any critical flaws or objections")
        print("4. DECIDE:")
        print("   - If valid → Proceed with Lean formalization")
        print("   - If minor issues → Address and re-validate")
        print("   - If major flaws → Return to research mode")
        print()
        print("DO NOT proceed with publication claims until validation is positive!")
        print()

    except Exception as e:
        print(f"Error during consultation: {e}")
        print()
        print("Fallback: Use manual validation (see above)")


def main():
    """Main entry point"""
    asyncio.run(validate_proof())


if __name__ == "__main__":
    main()
