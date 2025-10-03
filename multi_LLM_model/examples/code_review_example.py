#!/usr/bin/env python3
"""
Code Review Example - Multi-LLM Expert Consultation

This example demonstrates using multiple AI models to review code,
aggregating their feedback for comprehensive analysis.
"""

import asyncio
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from claude_llm_bridge import MultiLLMBridge


async def review_code(code_snippet, language="Python", focus_areas=None):
    """
    Get code review from multiple AI experts

    Args:
        code_snippet: The code to review
        language: Programming language
        focus_areas: List of specific areas to focus on (optional)
    """

    bridge = MultiLLMBridge()

    # Build the review prompt
    focus_text = ""
    if focus_areas:
        focus_text = "\nSpecifically focus on:\n" + "\n".join(f"- {area}" for area in focus_areas)

    prompt = f"""
Please review this {language} code for:
1. Bugs and potential errors
2. Performance issues
3. Security vulnerabilities
4. Code quality and best practices
5. Readability and maintainability
{focus_text}

CODE TO REVIEW:
```{language.lower()}
{code_snippet}
```

Provide specific suggestions with explanations.
"""

    print(f"Submitting code for review by AI expert panel...")
    print("=" * 60)

    # Get reviews from all experts
    responses = await bridge.consult_all_experts(prompt)

    # Analyze consensus
    successful = [r for r in responses if r['success']]

    print(f"\nReceived {len(successful)}/{len(responses)} expert reviews\n")

    # Print each expert's review
    for i, response in enumerate(successful, 1):
        print(f"{'=' * 60}")
        print(f"REVIEW #{i} - {response['source'].upper()}")
        print(f"{'=' * 60}")
        print(response['content'])
        print()

    # Synthesize recommendations
    synthesis = bridge.synthesize_responses(responses)

    return {
        'reviews': successful,
        'synthesis': synthesis,
        'consensus': len(set(r['content'][:100] for r in successful)) < len(successful)  # Simple similarity check
    }


async def main():
    """Example: Review a Python function"""

    # Example code with intentional issues
    code = '''
def calculate_average(numbers):
    total = 0
    for num in numbers:
        total = total + num
    return total / len(numbers)

# Usage
values = [10, 20, 30, 40, 50]
avg = calculate_average(values)
print(avg)
'''

    result = await review_code(
        code_snippet=code,
        language="Python",
        focus_areas=[
            "Edge cases (empty list, division by zero)",
            "Performance optimization opportunities",
            "Python idioms and best practices"
        ]
    )

    print("\n" + "=" * 60)
    print("REVIEW SUMMARY")
    print("=" * 60)
    print(f"Total reviews received: {len(result['reviews'])}")
    print(f"Consensus detected: {'Yes' if result['consensus'] else 'Diverse opinions'}")

    # Show common themes if available
    if result['synthesis']['synthesis_success']:
        recs = result['synthesis']['recommendations']
        print(f"\nRecommendations extracted:")
        for key, values in recs.items():
            if values:
                print(f"  - {key}: {len(values)} suggestions")


if __name__ == "__main__":
    asyncio.run(main())
