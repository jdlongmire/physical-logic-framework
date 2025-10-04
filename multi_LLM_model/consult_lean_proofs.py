#!/usr/bin/env python3
"""
Lean 4 Proof Consultation - Multi-LLM Expert Panel
"""

import asyncio
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from claude_llm_bridge import MultiLLMBridge


async def main():
    """Consult AI experts on Lean 4 proof strategies"""

    # Read the query from file
    query_file = "lean_proof_query.md"
    with open(query_file, 'r') as f:
        prompt = f.read()

    print("=" * 80)
    print("MULTI-LLM EXPERT CONSULTATION: Lean 4 Proof Strategies")
    print("=" * 80)
    print(f"\nQuerying Grok-3, GPT-4, and Gemini-2.0 in parallel...")
    print(f"Query length: {len(prompt)} characters\n")

    try:
        # Initialize bridge
        bridge = MultiLLMBridge()

        # Query all experts concurrently
        responses = await bridge.consult_all_experts(prompt)

        # Synthesize responses
        synthesis = bridge.synthesize_responses(responses)

        # Print synthesis summary
        print("\n" + "=" * 80)
        print("SYNTHESIS & RECOMMENDATIONS")
        print("=" * 80)
        bridge.print_synthesis_summary(synthesis)

        # Print individual responses
        print("\n" + "=" * 80)
        print("DETAILED EXPERT RESPONSES")
        print("=" * 80)

        for response in responses:
            if response['success']:
                print(f"\n{'='*80}")
                print(f"{response['source'].upper()} ({response['model']})")
                print(f"{'='*80}")
                print(response['content'])
                print()
            else:
                print(f"\n{response['source'].upper()}: FAILED")
                print(f"Error: {response.get('error', 'Unknown error')}\n")

        # Save consultation log
        log_file = bridge.save_consultation_log({
            'prompt': prompt,
            'responses': responses,
            'synthesis': synthesis,
            'domain': 'lean4_formal_verification',
            'context': 'N=3_constraint_enumeration_proofs'
        }, filename='lean_proof_consultation.json')

        print("\n" + "=" * 80)
        print(f"Full consultation log saved to: {log_file}")
        print("=" * 80)

        # Summary statistics
        successful = sum(1 for r in responses if r['success'])
        print(f"\nConsultation complete: {successful}/3 experts responded successfully")

        return synthesis, responses

    except FileNotFoundError as e:
        if 'api_config.json' in str(e):
            print("\n⚠️  ERROR: api_config.json not found")
            print("\nThe multi-LLM system requires API keys to function.")
            print("Please create api_config.json from api_config_template.json")
            print("and add your API keys for Grok, OpenAI, and Google AI.\n")
            return None, None
        raise
    except Exception as e:
        print(f"\n❌ Error during consultation: {e}")
        import traceback
        traceback.print_exc()
        return None, None


if __name__ == "__main__":
    asyncio.run(main())
