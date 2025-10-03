#!/usr/bin/env python3
"""
Research Assistant Example - Multi-LLM Expert Consultation

This example shows how to use the multi-LLM system for research tasks,
getting diverse perspectives on technical topics.
"""

import asyncio
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from claude_llm_bridge import MultiLLMBridge


async def research_topic(topic, specific_questions=None):
    """
    Research a topic using multiple AI perspectives

    Args:
        topic: The main research topic
        specific_questions: Optional list of specific questions to explore
    """

    bridge = MultiLLMBridge()

    # Build comprehensive research prompt
    prompt = f"""
RESEARCH TOPIC: {topic}

Please provide a comprehensive analysis including:
1. Key concepts and fundamentals
2. Current state of the art
3. Common approaches and best practices
4. Trade-offs and considerations
5. Practical recommendations
"""

    if specific_questions:
        prompt += "\n\nSpecific questions to address:\n"
        prompt += "\n".join(f"- {q}" for q in specific_questions)

    print(f"Researching topic: {topic}")
    print("Consulting AI expert panel...")
    print("=" * 60)

    # Get diverse expert perspectives
    responses = await bridge.consult_all_experts(prompt)

    # Synthesize findings
    synthesis = bridge.synthesize_responses(responses)

    return {
        'topic': topic,
        'responses': responses,
        'synthesis': synthesis
    }


async def comparative_analysis(option_a, option_b, context=""):
    """
    Get expert opinions comparing two approaches/technologies/solutions

    Args:
        option_a: First option to compare
        option_b: Second option to compare
        context: Additional context about the comparison
    """

    bridge = MultiLLMBridge()

    prompt = f"""
COMPARATIVE ANALYSIS

Option A: {option_a}
Option B: {option_b}

{f'Context: {context}' if context else ''}

Please provide:
1. Detailed comparison of both options
2. Pros and cons of each
3. Use cases where each excels
4. Recommendation with clear rationale
5. Implementation considerations

Be specific and provide actionable insights.
"""

    print(f"\nComparing: {option_a} vs {option_b}")
    print("=" * 60)

    responses = await bridge.consult_all_experts(prompt)

    # Show each expert's perspective
    successful = [r for r in responses if r['success']]

    print(f"\nReceived {len(successful)}/3 expert analyses\n")

    for response in successful:
        print(f"\n{response['source'].upper()}'s Analysis:")
        print("-" * 60)
        # Print first 500 chars as preview
        preview = response['content'][:500]
        print(preview + "..." if len(response['content']) > 500 else preview)

    synthesis = bridge.synthesize_responses(responses)

    # Check for consensus
    recommendations = [r['content'].lower() for r in successful]
    option_a_votes = sum('option a' in rec or option_a.lower() in rec for rec in recommendations)
    option_b_votes = sum('option b' in rec or option_b.lower() in rec for rec in recommendations)

    print("\n" + "=" * 60)
    print("EXPERT CONSENSUS:")
    if option_a_votes > option_b_votes:
        print(f"Majority favor: {option_a} ({option_a_votes}/3 experts)")
    elif option_b_votes > option_a_votes:
        print(f"Majority favor: {option_b} ({option_b_votes}/3 experts)")
    else:
        print("No clear consensus - diverse opinions (review full responses)")

    return {
        'option_a': option_a,
        'option_b': option_b,
        'responses': successful,
        'synthesis': synthesis,
        'consensus': abs(option_a_votes - option_b_votes) >= 2
    }


async def main():
    """Example research scenarios"""

    print("\n" + "#" * 60)
    print("# EXAMPLE 1: Technical Topic Research")
    print("#" * 60)

    result1 = await research_topic(
        topic="Database Indexing Strategies",
        specific_questions=[
            "When should I use B-tree vs Hash indexes?",
            "How do composite indexes work?",
            "What are the performance trade-offs?"
        ]
    )

    print("\n\nRESEARCH FINDINGS:")
    print("=" * 60)
    for response in result1['responses']:
        if response['success']:
            print(f"\n{response['source'].upper()}:")
            print(response['content'][:300] + "...")

    print("\n\n" + "#" * 60)
    print("# EXAMPLE 2: Comparative Analysis")
    print("#" * 60)

    result2 = await comparative_analysis(
        option_a="Microservices Architecture",
        option_b="Monolithic Architecture",
        context="Building a new e-commerce platform with 10 developers, expecting 100K users in first year"
    )

    # Results already printed in comparative_analysis function

    print("\n\n" + "=" * 60)
    print("SESSION SUMMARY")
    print("=" * 60)
    print(f"Topics researched: 2")
    print(f"Total expert consultations: {len(result1['responses']) + len(result2['responses'])}")
    print(f"Successful responses: {sum(1 for r in result1['responses'] + result2['responses'] if r['success'])}")


if __name__ == "__main__":
    asyncio.run(main())
