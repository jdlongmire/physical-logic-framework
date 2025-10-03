# Multi-LLM Expert Consultation System

## Overview

The Multi-LLM system provides parallel consultation across multiple AI experts (Grok, ChatGPT, Gemini) for Logic Field Theory development, specializing in Lean 4 formal verification challenges.

**Architecture Note**: This system supplements Claude Code (your primary development assistant) by providing additional expert perspectives when needed. Claude Code handles direct development work, while the multi-LLM team offers diverse opinions for complex problems.

## Status: ✅ FULLY OPERATIONAL

**All 3 APIs Working:**
- ✅ Grok (Grok-3 model)
- ✅ ChatGPT (GPT-4 model)
- ✅ Gemini (Gemini-2.0-flash-exp model)

**Features:**
- ✅ Parallel consultation (async requests)
- ✅ Response synthesis with recommendation extraction
- ✅ Lean 4 vs Lean 3 validation
- ✅ Comprehensive test suite
- ✅ Session logging

## Quick Start

### 1. Configuration

```bash
# Copy template and add your API keys
cp api_config_template.json api_config.json
# Edit api_config.json with your keys (NEVER commit this file!)
```

### 2. Test All APIs

```bash
cd multi_LLM
python3 test_suite.py
```

Expected output:
```
Overall Results: 6/6 tests passed

API Status:
  Grok:    [OK] Working
  ChatGPT: [OK] Working
  Gemini:  [OK] Working
```

### 3. Use for Lean 4 Consultation

```python
import asyncio
from claude_llm_bridge import MultiLLMBridge

async def main():
    bridge = MultiLLMBridge()

    # Consult all experts
    result = await bridge.lean_mvt_consultation(
        theorem_code="theorem example ...",
        issue_description="How to prove monotonicity?",
        context="Working with Lean 4.23.0-rc2"
    )

    # Print synthesis
    bridge.print_synthesis_summary(result['synthesis'])

    # Save detailed log
    log_file = bridge.save_consultation_log(result)
    print(f"Saved to: {log_file}")

asyncio.run(main())
```

## Current Configuration

### API Endpoints
- **Grok**: `https://api.x.ai/v1/chat/completions`
- **ChatGPT**: `https://api.openai.com/v1/chat/completions`
- **Gemini**: `https://generativelanguage.googleapis.com/v1beta/models/gemini-2.0-flash-exp:generateContent`

### Settings
- Temperature: 0.1 (focused responses)
- Max tokens: 4000
- Timeout: 30 seconds

### Lean 4 System Prompt
Experts are configured with:
- Lean 4.23.0-rc2 environment awareness
- Mathlib rev 5b9937fc4ef27c6ccd8a03b302335e0004185ed4
- Formal verification expertise
- Quantum mechanics domain knowledge

## Features in Detail

### 1. Parallel Consultation
Queries all 3 experts simultaneously for fastest results.

```python
responses = await bridge.consult_all_experts("Your question here")
```

### 2. Response Synthesis
Automatically extracts:
- MVT approaches
- Mathlib theorem suggestions
- Alternative strategies
- Lean code snippets

### 3. Lean 4 Validation
Detects and warns about Lean 3 syntax in responses:
- Checks for `import analysis.*` vs `import Mathlib.*`
- Detects `begin...end` vs `by`
- Flags `cases'` vs `obtain`
- Counts syntax indicators

### 4. Session Logging
All consultations saved to `consultation_log_[timestamp].json` (gitignored).

## File Structure

```
multi_LLM/
├── README.md                    # This file
├── api_config_template.json     # Template for API keys
├── api_config.json             # Your keys (gitignored!)
├── claude_llm_bridge.py        # Main bridge class
├── test_suite.py               # Comprehensive test suite
├── lean4_training_prompt.md    # Training prompt for experts
└── test_results.json           # Latest test results
```

## Test Suite

Run `python3 test_suite.py` to validate:

1. **Configuration Test** - API keys and endpoints loaded correctly
2. **Individual API Tests** - Each expert responds properly
3. **Parallel Consultation** - All experts queried simultaneously
4. **Response Synthesis** - Recommendations extracted correctly

Results saved to `test_results.json`.

## Lean 4 Training Protocol

To ensure experts provide Lean 4 (not Lean 3) advice:

1. **Pre-consultation training**: Use `lean4_training_prompt.md`
2. **Familiarize with environment**:
   - Lean 4.23.0-rc2
   - Mathlib revision 5b9937fc
   - Correct theorem names (`exists_deriv_eq_slope` vs Lean 3 equivalents)

3. **Validation**: Automatic Lean 3 detection flags incorrect syntax

## Usage Patterns

### For Lean 4 Compilation Errors
```python
result = await bridge.lean_mvt_consultation(
    theorem_code=error_code,
    issue_description="Compilation error: [paste error]",
    context="Using Mathlib.Analysis.Calculus.MeanValue"
)
```

### For Proof Strategy
```python
prompt = "Best approach to prove monotonicity from positive derivative in Lean 4?"
responses = await bridge.consult_all_experts(prompt)
synthesis = bridge.synthesize_responses(responses)
```

### For Mathlib Discovery
```python
prompt = """
What Mathlib theorems exist for:
1. Mean Value Theorem (Lean 4.23.0-rc2)
2. Monotonicity from derivatives
3. Provide exact import statements
"""
responses = await bridge.consult_all_experts(prompt)
```

## Troubleshooting

### API Failures

**Grok failing:**
1. Verify API key: `xai-[your-key]`
2. Check https://api.x.ai is accessible
3. Check rate limits

**ChatGPT failing:**
1. Verify API key: `sk-proj-[your-key]`
2. Check OpenAI service status
3. Verify sufficient credits

**Gemini failing:**
1. Verify API key format
2. Try different model: `gemini-1.5-pro` or `gemini-2.0-flash-exp`
3. Check Google AI service status

### Lean 3 Responses

If experts provide Lean 3 advice:
1. Check validation warnings in synthesis
2. Explicitly mention "Lean 4.23.0-rc2" in prompt
3. Reference `lean4_training_prompt.md` for context
4. Ask for "Mathlib 4" specifically

## Integration with Project

### Session Start Checklist
```bash
# 1. Test multi-LLM system
cd multi_LLM && python3 test_suite.py

# 2. If any failures, check API keys
cat api_config.json  # Should have valid keys

# 3. Ready to consult experts
python3 claude_llm_bridge.py "Your Lean 4 question"
```

### With Sorry Elimination Workflow

Per `.claude/sorry_elimination_lessons_learned.md`:
- **Default to team consultation** for any sorry > 5 minutes
- Use multi-LLM for:
  - Complex type errors
  - Mathematical proofs (MVT, combinatorics)
  - Mathlib integration
  - Proof strategy planning

## Security Notes

⚠️ **NEVER commit `api_config.json`** - Contains API keys!

- Template: `api_config_template.json` (committed)
- Your keys: `api_config.json` (gitignored)
- Logs: `consultation_log_*.json` (gitignored)

## Performance

- **Parallel requests**: ~2-5 seconds for all 3 experts
- **Sequential**: Would be ~6-15 seconds
- **Success rate**: 100% when all APIs configured correctly
- **Synthesis quality**: Excellent with multiple expert perspectives

## Latest Test Results

```json
{
  "api_results": {
    "grok": true,
    "chatgpt": true,
    "gemini": true
  },
  "parallel_ok": true,
  "synthesis_ok": true
}
```

**Test Date**: 2025-10-03
**Status**: All systems operational

## Development Architecture

**Primary Development**: Claude Code (direct interaction)
- Direct code execution and repository access
- Real-time file editing and tool usage
- Full session context and continuity
- Your main development assistant

**Supplemental Consultation**: Multi-LLM Team (parallel queries)
- Grok: Mathematical formalization, advanced tactics
- ChatGPT: Mathlib navigation, proof strategy
- Gemini: Combinatorics, alternative approaches
- Use when you need multiple expert perspectives

**When to Use Multi-LLM**:
- Complex Lean 4 problems with no obvious solution
- Need validation from multiple sources
- Exploring different proof strategies
- Discovering Mathlib theorems and patterns

**When to Use Claude Code (me) Directly**:
- File editing and repository operations
- Systematic development tasks
- Build management and debugging
- Session management and documentation

## Future Enhancements

1. **Caching** - Store common Mathlib queries to avoid redundant API calls
2. **Auto-training** - Automatically send Lean 4 context on first consultation
3. **Retry logic** - Exponential backoff for rate limits
4. **Response ranking** - Score responses by Lean 4 accuracy
5. **Context injection** - Auto-include recent Lean errors in prompts

---

**Maintainer**: James D. Longmire
**Last Updated**: 2025-10-03
**Status**: Production-ready for LFT formal verification
