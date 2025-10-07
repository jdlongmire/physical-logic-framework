#!/usr/bin/env python3
"""
Multi-LLM Consultation: Logic Realism Foundational Paper Peer Review

Consults Grok-3, GPT-4, and Gemini-2.0 for rigorous peer review of the
Logic Field Theory Ia paper establishing Logic Realism as scientific foundation.
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


def load_peer_review_query():
    """Load the Logic Realism peer review query"""
    query_file = Path(__file__).parent / "logic_realism_peer_review.md"
    if not query_file.exists():
        raise FileNotFoundError(f"Peer review query file not found: {query_file}")

    with open(query_file, 'r', encoding='utf-8') as f:
        query = f.read()

    # Load the actual paper text to append
    paper_file = Path(__file__).parent.parent / "paper" / "Logic_Realism_Foundational_Paper.md"
    if paper_file.exists():
        with open(paper_file, 'r', encoding='utf-8') as f:
            paper_text = f.read()

        # Append paper text to query
        query += "\n\n---\n\n## FULL PAPER TEXT\n\n"
        query += paper_text
    else:
        print(f"Warning: Paper file not found at {paper_file}")
        print("Proceeding with summary-only review query")

    return query


async def consult_on_logic_realism_review():
    """Run multi-LLM peer review consultation on Logic Realism paper"""

    print("=" * 80)
    print("LOGIC REALISM FOUNDATIONAL PAPER - MULTI-LLM PEER REVIEW")
    print("=" * 80)
    print()

    # Load peer review query
    try:
        query = load_peer_review_query()
        print(f"Loaded peer review query with full paper text ({len(query)} characters)")
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
        print("Alternatively, you can paste the peer review query from:")
        print(f"  {Path(__file__).parent / 'logic_realism_peer_review.md'}")
        print()
        print("Into ChatGPT, Claude, or other LLM interfaces manually.")
        return

    # Initialize bridge
    bridge = MultiLLMBridge()

    print()
    print("Consulting expert LLM reviewers (this may take 60-120 seconds)...")
    print()

    # Run consultation
    try:
        responses = await bridge.consult_all_experts(
            prompt=query,
            max_tokens=16000,  # Long detailed review needed
            temperature=0.2    # Keep reviews focused and rigorous
        )

        # Save individual reviews
        output_dir = Path(__file__).parent / "consultation_results"
        output_dir.mkdir(exist_ok=True)

        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

        for model, response in responses.items():
            filename = output_dir / f"logic_realism_review_{model}_{timestamp}.md"
            with open(filename, 'w', encoding='utf-8') as f:
                f.write(f"# Logic Realism Paper Peer Review - {model.upper()}\n\n")
                f.write(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
                f.write(f"**Paper**: Logic Field Theory Ia: Logic Realism as Foundational Framework\n\n")
                f.write("---\n\n")
                f.write(response)

            print(f"✓ Saved {model} review: {filename}")

        # Synthesize reviews
        print()
        print("Synthesizing peer reviews...")
        synthesis = bridge.synthesize_responses(responses)

        # Save synthesis
        synthesis_file = output_dir / f"logic_realism_review_synthesis_{timestamp}.md"
        with open(synthesis_file, 'w', encoding='utf-8') as f:
            f.write("# Logic Realism Paper - Multi-LLM Peer Review Synthesis\n\n")
            f.write(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
            f.write(f"**Paper**: Logic Field Theory Ia: Logic Realism as Foundational Framework\n\n")
            f.write("---\n\n")
            f.write(synthesis)

        print(f"✓ Saved synthesis: {synthesis_file}")

        # Print summary
        print()
        print("=" * 80)
        print("PEER REVIEW COMPLETE")
        print("=" * 80)
        print()
        print(f"Results saved to: {output_dir}")
        print()
        print("Review files:")
        print("  - Individual reviews from Grok-3, GPT-4, Gemini-2.0")
        print("  - Synthesis document with consensus recommendations")
        print()
        print("Next steps:")
        print("1. Read individual reviews for specific technical feedback")
        print("2. Review synthesis for consensus on strengths/weaknesses")
        print("3. Address any major revisions identified")
        print("4. Incorporate minor corrections as needed")
        print("5. Prepare response to reviewers if needed")

    except Exception as e:
        print(f"Error during consultation: {e}")
        print()
        print("You can still use the peer review query manually:")
        print(f"  {Path(__file__).parent / 'logic_realism_peer_review.md'}")
        print()
        print("Paste into your preferred LLM interface for manual review.")


def main():
    """Main entry point"""
    asyncio.run(consult_on_logic_realism_review())


if __name__ == "__main__":
    main()
