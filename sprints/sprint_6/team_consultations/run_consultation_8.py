#!/usr/bin/env python3
"""
Run Team Consultation 8: Peer Review of Born Rule Non-Circularity Module
Sprint 6 Day 4 - Final validation before moving forward
"""

import sys
import os
import json
import asyncio
from datetime import datetime

# Add multi_LLM to path
sys.path.insert(0, 'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/multi_LLM')

from enhanced_llm_bridge import EnhancedMultiLLMBridge, QueryType

async def run_consultation_8():
    """Run consultation 8 for peer review of completed Born Rule module."""

    # Initialize bridge
    print("Initializing Multi-LLM Bridge...")
    bridge = EnhancedMultiLLMBridge(
        config_path='C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/multi_LLM/api_config.json'
    )

    # Read prompt
    prompt_path = 'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/sprints/sprint_6/team_consultations/consultation_8_peer_review_prompt.txt'
    with open(prompt_path, 'r', encoding='utf-8') as f:
        prompt = f.read()

    print("\n" + "="*70)
    print("TEAM CONSULTATION 8: Born Rule Module Peer Review")
    print("="*70)
    print("\nFocus: Final validation of BornRuleNonCircularity.lean")
    print("Status: 0 sorry statements, 100% computational validation")
    print("Goal: Team consensus for production readiness")
    print("\nRunning consultation (this may take a minute)...\n")

    # Run consultation with peer review query type
    result = await bridge.consult_peer_review(
        section=prompt,
        focus_area="Born Rule non-circularity module - axiomatization strategy and theoretical soundness"
    )

    # Print results with scores
    bridge.print_results_with_scores(result)

    # Save detailed results
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Save JSON
    json_path = f'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/sprints/sprint_6/team_consultations/consultation_8_{timestamp}.json'
    with open(json_path, 'w', encoding='utf-8') as f:
        json.dump(result, f, indent=2, ensure_ascii=False)

    # Save formatted text
    txt_path = f'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/sprints/sprint_6/team_consultations/consultation_8_{timestamp}.txt'
    with open(txt_path, 'w', encoding='utf-8') as f:
        f.write("="*70 + "\n")
        f.write("TEAM CONSULTATION 8: Born Rule Module Peer Review\n")
        f.write("="*70 + "\n\n")
        f.write("Module: PhysicalLogicFramework.Foundations.BornRuleNonCircularity\n")
        f.write("Status: 0 sorry statements, 100% complete\n\n")
        f.write(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Query Type: {result.get('query_type', 'code_review')}\n")
        f.write(f"From Cache: {result.get('from_cache', False)}\n\n")

        responses = result.get('responses', [])
        quality_scores = result.get('quality_scores', {})

        for i, response in enumerate(responses, 1):
            source = response.get('source', 'unknown')
            success = response.get('success', False)

            f.write("="*70 + "\n")
            f.write(f"{i}. {source.upper()} REVIEW\n")
            f.write("="*70 + "\n\n")

            if success:
                overall_score = response.get('quality_score', 0.0)
                f.write(f"Quality Score: {overall_score:.2f}/1.0\n")

                # Interpret score
                if overall_score >= 0.90:
                    f.write("Assessment: ACCEPT (Excellent)\n\n")
                elif overall_score >= 0.70:
                    f.write("Assessment: ACCEPT / MINOR REVISION\n\n")
                elif overall_score >= 0.50:
                    f.write("Assessment: MINOR / MAJOR REVISION\n\n")
                elif overall_score >= 0.30:
                    f.write("Assessment: MAJOR REVISION\n\n")
                else:
                    f.write("Assessment: REJECT\n\n")

                # Detailed scores
                if source in quality_scores:
                    scores = quality_scores[source]
                    f.write("Dimension Scores:\n")
                    for dim, val in scores.items():
                        if val > 0:
                            f.write(f"  - {dim}: {val:.2f}\n")
                    f.write("\n")

                # Full response
                f.write("Detailed Review:\n")
                f.write("-"*70 + "\n")
                f.write(response.get('content', ''))
                f.write("\n\n")
            else:
                f.write(f"[FAILED] Error: {response.get('error', 'Unknown error')}\n\n")

        # Summary and consensus
        f.write("="*70 + "\n")
        f.write("PEER REVIEW SUMMARY\n")
        f.write("="*70 + "\n\n")

        successful = [r for r in responses if r.get('success')]
        if successful:
            avg_score = sum(r.get('quality_score', 0) for r in successful) / len(successful)
            f.write(f"Average Quality Score: {avg_score:.2f}/1.0\n")
            f.write(f"Target Threshold: 0.70/1.0 (Accept/Minor Revision)\n\n")

            # Team consensus
            if avg_score >= 0.90:
                f.write("TEAM CONSENSUS: ACCEPT (Excellent work)\n")
            elif avg_score >= 0.70:
                f.write("TEAM CONSENSUS: ACCEPT / MINOR REVISION\n")
            elif avg_score >= 0.50:
                f.write("TEAM CONSENSUS: MINOR / MAJOR REVISION NEEDED\n")
            elif avg_score >= 0.30:
                f.write("TEAM CONSENSUS: MAJOR REVISION REQUIRED\n")
            else:
                f.write("TEAM CONSENSUS: REJECT - SUBSTANTIAL REWORK NEEDED\n")

            f.write(f"\nSuccessful Reviews: {len(successful)}/{len(responses)}\n\n")

            # Individual assessments
            f.write("Individual Scores:\n")
            for r in sorted(successful, key=lambda x: x.get('quality_score', 0), reverse=True):
                score = r.get('quality_score', 0)
                assessment = "ACCEPT" if score >= 0.70 else "REVISION" if score >= 0.30 else "REJECT"
                f.write(f"  - {r['source'].upper()}: {score:.2f}/1.0 ({assessment})\n")

            if result.get('best_response'):
                best = result['best_response']
                f.write(f"\nLead Reviewer: {best['source'].upper()} ({best['quality']:.2f}/1.0)\n")

    # Print summary
    print("\n" + "="*70)
    print("PEER REVIEW SUMMARY")
    print("="*70)

    successful = [r for r in result.get('responses', []) if r.get('success')]
    if successful:
        avg_score = sum(r.get('quality_score', 0) for r in successful) / len(successful)
        print(f"\nAverage Quality Score: {avg_score:.2f}/1.0")
        print(f"Target Threshold: 0.70/1.0 (Accept/Minor Revision)")

        if avg_score >= 0.90:
            print(f"\n[SUCCESS] ✓ TEAM CONSENSUS: ACCEPT (Excellent)")
        elif avg_score >= 0.70:
            print(f"\n[SUCCESS] ✓ TEAM CONSENSUS: ACCEPT / MINOR REVISION")
        elif avg_score >= 0.50:
            print(f"\n[INFO] Team recommends: MINOR / MAJOR REVISION")
        elif avg_score >= 0.30:
            print(f"\n[WARNING] Team recommends: MAJOR REVISION")
        else:
            print(f"\n[CRITICAL] Team recommends: REJECT")

        print(f"\nSuccessful Reviews: {len(successful)}/{len(result.get('responses', []))}")

        # Show individual scores
        print("\nIndividual Assessments:")
        for r in sorted(successful, key=lambda x: x.get('quality_score', 0), reverse=True):
            score = r.get('quality_score', 0)
            assessment = "ACCEPT" if score >= 0.70 else "REVISION" if score >= 0.30 else "REJECT"
            print(f"  - {r['source'].upper()}: {score:.2f}/1.0 ({assessment})")

    print(f"\nResults saved:")
    print(f"  - JSON: {json_path}")
    print(f"  - Text: {txt_path}")

    # Cache stats
    stats = bridge.get_cache_stats()
    print(f"\nCache Stats:")
    print(f"  - Hit Rate: {stats.get('hit_rate', 0):.1%}")
    print(f"  - Total Entries: {stats.get('total_entries', 0)}")

    print("\n" + "="*70)
    print("REVIEW INTERPRETATION")
    print("="*70)
    print("\nScore Guide:")
    print("  0.90-1.00: ACCEPT (Production ready)")
    print("  0.70-0.89: ACCEPT / MINOR REVISION (Small fixes)")
    print("  0.50-0.69: MINOR / MAJOR REVISION (Moderate work)")
    print("  0.30-0.49: MAJOR REVISION (Substantial rework)")
    print("  0.00-0.29: REJECT (Fundamental issues)")
    print("\nNext Steps:")
    print("  1. Review detailed feedback from each reviewer")
    print("  2. Address any critical concerns or gaps")
    print("  3. Implement minor revisions if needed")
    print("  4. Update documentation and commit changes")

    return result

if __name__ == "__main__":
    result = asyncio.run(run_consultation_8())
