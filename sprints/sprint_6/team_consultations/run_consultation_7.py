#!/usr/bin/env python3
"""
Run Team Consultation 7: Tactical Lean 4 Guidance for Key Lemma
Sprint 6 Day 4 - Get specific help on hardest piece: distance_and_entropy_implies_left_multiplication
"""

import sys
import os
import json
import asyncio
from datetime import datetime

# Add multi_LLM to path
sys.path.insert(0, 'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/multi_LLM')

from enhanced_llm_bridge import EnhancedMultiLLMBridge, QueryType

async def run_consultation_7():
    """Run consultation 7 for tactical Lean 4 guidance on hardest lemma."""

    # Initialize bridge
    print("Initializing Multi-LLM Bridge...")
    bridge = EnhancedMultiLLMBridge(
        config_path='C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/multi_LLM/api_config.json'
    )

    # Read prompt
    prompt_path = 'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/sprints/sprint_6/team_consultations/consultation_7_prompt.txt'
    with open(prompt_path, 'r', encoding='utf-8') as f:
        prompt = f.read()

    print("\n" + "="*70)
    print("TEAM CONSULTATION 7: Tactical Lean 4 Guidance (Key Lemma)")
    print("="*70)
    print("\nFocus: distance_and_entropy_implies_left_multiplication")
    print("Goal: Get specific Lean 4 tactics and Mathlib guidance")
    print("\nRunning consultation (this may take a minute)...\n")

    # Run consultation with Lean proof query type
    result = await bridge.consult_lean_proof(
        code=prompt,
        issue="Need tactical Lean 4 guidance for hardest lemma: showing entropy preservation forces g⁻¹ = 1",
        context="All theorem structures complete, this is the final hard piece blocking completion"
    )

    # Print results with scores
    bridge.print_results_with_scores(result)

    # Save detailed results
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Save JSON
    json_path = f'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/sprints/sprint_6/team_consultations/consultation_7_{timestamp}.json'
    with open(json_path, 'w', encoding='utf-8') as f:
        json.dump(result, f, indent=2, ensure_ascii=False)

    # Save formatted text
    txt_path = f'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/sprints/sprint_6/team_consultations/consultation_7_{timestamp}.txt'
    with open(txt_path, 'w', encoding='utf-8') as f:
        f.write("="*70 + "\n")
        f.write("TEAM CONSULTATION 7: Tactical Lean 4 Guidance (Key Lemma)\n")
        f.write("="*70 + "\n\n")
        f.write("Focus: distance_and_entropy_implies_left_multiplication\n")
        f.write("The hardest piece - novel mathematical insight\n\n")
        f.write(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Query Type: {result.get('query_type', 'lean_proof')}\n")
        f.write(f"From Cache: {result.get('from_cache', False)}\n\n")

        responses = result.get('responses', [])
        quality_scores = result.get('quality_scores', {})

        for i, response in enumerate(responses, 1):
            source = response.get('source', 'unknown')
            success = response.get('success', False)

            f.write("="*70 + "\n")
            f.write(f"{i}. {source.upper()}\n")
            f.write("="*70 + "\n\n")

            if success:
                overall_score = response.get('quality_score', 0.0)
                f.write(f"Quality Score: {overall_score:.2f}/1.0\n\n")

                # Detailed scores
                if source in quality_scores:
                    scores = quality_scores[source]
                    f.write("Dimension Scores:\n")
                    for dim, val in scores.items():
                        if val > 0:
                            f.write(f"  - {dim}: {val:.2f}\n")
                    f.write("\n")

                # Full response
                f.write("Response:\n")
                f.write("-"*70 + "\n")
                f.write(response.get('content', ''))
                f.write("\n\n")
            else:
                f.write(f"[FAILED] Error: {response.get('error', 'Unknown error')}\n\n")

        # Summary
        f.write("="*70 + "\n")
        f.write("SUMMARY\n")
        f.write("="*70 + "\n\n")

        successful = [r for r in responses if r.get('success')]
        if successful:
            avg_score = sum(r.get('quality_score', 0) for r in successful) / len(successful)
            f.write(f"Average Quality Score: {avg_score:.2f}/1.0\n")
            f.write(f"Successful Responses: {len(successful)}/{len(responses)}\n\n")

            if result.get('best_response'):
                best = result['best_response']
                f.write(f"Best Response: {best['source'].upper()} ({best['quality']:.2f}/1.0)\n")

    # Print summary
    print("\n" + "="*70)
    print("CONSULTATION SUMMARY")
    print("="*70)

    successful = [r for r in result.get('responses', []) if r.get('success')]
    if successful:
        avg_score = sum(r.get('quality_score', 0) for r in successful) / len(successful)
        print(f"\nAverage Quality Score: {avg_score:.2f}/1.0")
        print(f"Target Threshold: 0.70/1.0")

        if avg_score >= 0.70:
            print(f"\n[SUCCESS] Score meets threshold!")
        else:
            print(f"\n[INFO] Score below threshold, but tactical guidance should still help")

        print(f"\nSuccessful Responses: {len(successful)}/{len(result.get('responses', []))}")

        # Show individual scores
        print("\nIndividual Scores:")
        for r in sorted(successful, key=lambda x: x.get('quality_score', 0), reverse=True):
            print(f"  - {r['source'].upper()}: {r.get('quality_score', 0):.2f}/1.0")

        # Lean-specific scoring
        print("\nLean Code Quality Breakdown:")
        for r in successful:
            source = r['source']
            if source in result.get('quality_scores', {}):
                lean_score = result['quality_scores'][source].get('lean_code_quality', 0)
                mathlib_score = result['quality_scores'][source].get('mathlib_citations', 0)
                print(f"  - {source.upper()}: Lean {lean_score:.2f}, Mathlib {mathlib_score:.2f}")

    print(f"\nResults saved:")
    print(f"  - JSON: {json_path}")
    print(f"  - Text: {txt_path}")

    # Cache stats
    stats = bridge.get_cache_stats()
    print(f"\nCache Stats:")
    print(f"  - Hit Rate: {stats.get('hit_rate', 0):.1%}")
    print(f"  - Total Entries: {stats.get('total_entries', 0)}")

    print("\n" + "="*70)
    print("KEY LEMMA FOCUS")
    print("="*70)
    print("\nLemma: distance_and_entropy_implies_left_multiplication")
    print("Challenge: Show entropy preservation forces g⁻¹ = 1")
    print("Impact: This is the novel insight blocking final completion")
    print("\nReview responses for:")
    print("  1. Recommended approach (A/B/C/other)")
    print("  2. Specific Lean 4 tactics")
    print("  3. Mathlib imports and theorems")
    print("  4. Code snippets with concrete moves")
    print("  5. Whether axiomatization is acceptable fallback")

    return result

if __name__ == "__main__":
    result = asyncio.run(run_consultation_7())
