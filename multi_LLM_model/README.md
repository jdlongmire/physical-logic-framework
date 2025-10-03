# Multi-LLM Expert Consultation System

## Overview

A Python framework for parallel consultation across multiple AI models (Grok, ChatGPT, Gemini) with automatic response synthesis and validation. Originally developed for formal verification in Lean 4, but applicable to any domain requiring diverse AI perspectives.

**Key Features**:
- ✅ Parallel API queries (3 experts simultaneously)
- ✅ Response synthesis and recommendation extraction
- ✅ Domain-specific validation (e.g., Lean 4 vs Lean 3 syntax)
- ✅ Comprehensive test suite
- ✅ Session logging and result tracking

---

## What This Package Provides

### Core Components

1. **`claude_llm_bridge.py`** - Main consultation framework
   - `MultiLLMBridge` class for managing multi-model queries
   - Async parallel API calls
   - Response synthesis with keyword extraction
   - Validation framework (customizable for your domain)

2. **`test_suite.py`** - Comprehensive testing
   - API connectivity tests
   - Parallel consultation verification
   - Response synthesis validation
   - Results logging

3. **`api_config_template.json`** - Configuration template
   - API endpoint definitions
   - Settings management
   - System prompt customization

---

## Quick Start

### 1. Installation

```bash
# Clone or copy this directory
cd multi_LLM_model

# Install dependencies
pip install aiohttp requests
```

**Requirements**:
- Python 3.7+
- `aiohttp` - Async HTTP client
- `requests` - HTTP library

### 2. Configuration

```bash
# Copy template and add your API keys
cp api_config_template.json api_config.json
```

**Edit `api_config.json`** and add your API keys:
```json
{
  "api_keys": {
    "grok": "xai-YOUR_GROK_API_KEY",
    "chatgpt": "sk-proj-YOUR_OPENAI_KEY",
    "gemini": "YOUR_GEMINI_KEY"
  }
}
```

⚠️ **SECURITY**: Never commit `api_config.json` to version control!

### 3. Test Your Setup

```bash
python test_suite.py
```

Expected output:
```
Overall Results: 6/6 tests passed

API Status:
  Grok:    [OK] Working
  ChatGPT: [OK] Working
  Gemini:  [OK] Working
```

### 4. Basic Usage

```python
import asyncio
from claude_llm_bridge import MultiLLMBridge

async def main():
    bridge = MultiLLMBridge()

    # Query all experts in parallel
    prompt = "What is the best way to implement binary search?"
    responses = await bridge.consult_all_experts(prompt)

    # Synthesize responses
    synthesis = bridge.synthesize_responses(responses)

    # Print summary
    bridge.print_synthesis_summary(synthesis)

    # Access individual responses
    for response in responses:
        if response['success']:
            print(f"\n{response['source'].upper()}:")
            print(response['content'][:200] + "...")

asyncio.run(main())
```

---

## Use Cases

### 1. Technical Problem Solving
Get multiple AI perspectives on complex technical problems:

```python
prompt = """
I need to optimize a database query that's running slow.
Current query: SELECT * FROM users WHERE status='active'
Table has 10M rows, no index on status.
What are the best approaches?
"""

responses = await bridge.consult_all_experts(prompt)
synthesis = bridge.synthesize_responses(responses)
```

### 2. Code Review
Validate solutions across different models:

```python
code = '''
def fibonacci(n):
    if n <= 1: return n
    return fibonacci(n-1) + fibonacci(n-2)
'''

prompt = f"Review this code and suggest improvements:\n{code}"
responses = await bridge.consult_all_experts(prompt)
```

### 3. Research & Exploration
Discover different approaches to the same problem:

```python
prompt = "What are the trade-offs between microservices and monolithic architecture?"
responses = await bridge.consult_all_experts(prompt)

# Get diverse perspectives
for response in responses:
    print(f"{response['source']}: {response['content']}")
```

---

## Customization

### Domain-Specific System Prompts

Edit `api_config.json` to customize expert behavior:

```json
{
  "lean_specific_prompts": {
    "system_prompt": "You are an expert in [YOUR DOMAIN]. Provide detailed, technically accurate solutions."
  }
}
```

Examples:
- **Web Development**: "You are a senior full-stack developer..."
- **Data Science**: "You are a data scientist specialized in ML..."
- **DevOps**: "You are a DevOps engineer expert in cloud infrastructure..."

### Custom Validation

Add your own validation logic in `claude_llm_bridge.py`:

```python
def validate_response(self, response_text: str) -> Dict[str, Any]:
    """Customize for your domain"""
    # Example: Check for Python 2 vs Python 3
    python2_indicators = ['print ', 'xrange', 'raw_input']
    python3_indicators = ['print(', 'range', 'input']

    # Your validation logic
    return {
        'is_valid': True,
        'warnings': []
    }
```

### Response Synthesis Keywords

Modify `synthesize_responses()` to extract domain-specific patterns:

```python
# Look for your domain keywords
if any(keyword in content for keyword in ['docker', 'kubernetes', 'container']):
    recommendations["devops_approaches"].append({
        "source": response['source'],
        "suggestion": response['content']
    })
```

---

## Advanced Features

### 1. Specialized Consultations

Create domain-specific consultation methods:

```python
async def devops_consultation(self, infrastructure_issue: str) -> Dict:
    """Specialized consultation for DevOps problems"""

    prompt = f"""
    INFRASTRUCTURE ISSUE: {infrastructure_issue}

    Please provide:
    1. Root cause analysis
    2. Immediate fixes
    3. Long-term solutions
    4. Best practices
    """

    responses = await self.consult_all_experts(prompt)
    synthesis = self.synthesize_responses(responses)

    return {
        'consultation_type': 'devops',
        'responses': responses,
        'synthesis': synthesis
    }
```

### 2. Session Logging

All consultations are automatically logged:

```python
# Save detailed consultation log
log_file = bridge.save_consultation_log(result, filename="my_session.json")
print(f"Saved to: {log_file}")
```

### 3. Batch Processing

Query multiple prompts efficiently:

```python
prompts = [
    "How to optimize React rendering?",
    "Best practices for API design?",
    "Database indexing strategies?"
]

results = []
for prompt in prompts:
    result = await bridge.consult_all_experts(prompt)
    results.append(result)
```

---

## Configuration Reference

### API Endpoints (Default)

```json
{
  "endpoints": {
    "grok": "https://api.x.ai/v1/chat/completions",
    "chatgpt": "https://api.openai.com/v1/chat/completions",
    "gemini": "https://generativelanguage.googleapis.com/v1beta/models/gemini-2.0-flash-exp:generateContent"
  }
}
```

### Settings

```json
{
  "default_settings": {
    "temperature": 0.1,      // 0.0-1.0: Lower = focused, Higher = creative
    "max_tokens": 4000,      // Maximum response length
    "timeout_seconds": 30    // API request timeout
  }
}
```

---

## Getting API Keys

### Grok (X.AI)
1. Visit https://x.ai/api
2. Sign up for API access
3. Generate API key (format: `xai-...`)

### ChatGPT (OpenAI)
1. Visit https://platform.openai.com/api-keys
2. Create API key (format: `sk-proj-...`)
3. Add payment method (pay-as-you-go)

### Gemini (Google)
1. Visit https://ai.google.dev/
2. Get API key from Google AI Studio
3. Enable Gemini API access

**Costs** (approximate):
- Grok: $5 per 1M input tokens
- ChatGPT (GPT-4): $30 per 1M input tokens
- Gemini: Free tier available, then $0.35 per 1M tokens

---

## Troubleshooting

### API Connection Failures

**Grok fails**:
```python
# Test connectivity
curl -X POST https://api.x.ai/v1/chat/completions \
  -H "Authorization: Bearer xai-YOUR_KEY" \
  -H "Content-Type: application/json" \
  -d '{"messages":[{"role":"user","content":"test"}],"model":"grok-3"}'
```

**ChatGPT fails**:
- Verify API key is active
- Check https://status.openai.com
- Ensure sufficient credits

**Gemini fails**:
- Try different model: `gemini-1.5-pro` vs `gemini-2.0-flash-exp`
- Verify API key permissions
- Check quota limits

### No Responses

```python
# Add debug output
import logging
logging.basicConfig(level=logging.DEBUG)

# Run consultation
responses = await bridge.consult_all_experts(prompt)
```

### Timeout Issues

Increase timeout in `api_config.json`:
```json
{
  "default_settings": {
    "timeout_seconds": 60
  }
}
```

---

## Example Projects

### Project 1: Multi-Model Code Review

```python
async def code_review_pipeline(code_snippet, language):
    bridge = MultiLLMBridge()

    prompt = f"""
    Review this {language} code for:
    1. Bugs and errors
    2. Performance issues
    3. Security vulnerabilities
    4. Best practices

    Code:
    {code_snippet}
    """

    responses = await bridge.consult_all_experts(prompt)

    # Aggregate findings
    all_issues = []
    for response in responses:
        if response['success']:
            # Extract issues (customize parsing)
            all_issues.append({
                'source': response['source'],
                'review': response['content']
            })

    return all_issues
```

### Project 2: Research Assistant

```python
async def research_topic(topic, depth='comprehensive'):
    bridge = MultiLLMBridge()

    questions = [
        f"What are the fundamentals of {topic}?",
        f"What are current trends in {topic}?",
        f"What are best practices for {topic}?",
        f"What are common pitfalls in {topic}?"
    ]

    research = {}
    for question in questions:
        responses = await bridge.consult_all_experts(question)
        research[question] = bridge.synthesize_responses(responses)

    return research
```

### Project 3: Decision Support System

```python
async def technical_decision(options, criteria):
    bridge = MultiLLMBridge()

    prompt = f"""
    I need to choose between: {', '.join(options)}

    Criteria:
    {criteria}

    Provide:
    1. Pros and cons of each option
    2. Recommendation with rationale
    3. Implementation considerations
    """

    responses = await bridge.consult_all_experts(prompt)
    synthesis = bridge.synthesize_responses(responses)

    # Consensus or divergence?
    recommendations = [r['content'] for r in responses if r['success']]

    return {
        'consensus': len(set(recommendations)) == 1,
        'recommendations': recommendations,
        'synthesis': synthesis
    }
```

---

## Best Practices

### 1. Prompt Engineering

**Good Prompt**:
```python
prompt = """
PROBLEM: API latency increased from 100ms to 500ms after deployment

CONTEXT:
- Microservices architecture
- 10k requests/minute
- Added new caching layer yesterday

REQUIREMENTS:
1. Identify likely causes
2. Suggest diagnostic steps
3. Propose solutions with trade-offs
"""
```

**Poor Prompt**:
```python
prompt = "API is slow, help?"
```

### 2. Response Validation

Always validate before using AI suggestions:
```python
responses = await bridge.consult_all_experts(prompt)

# Check consensus
successful = [r for r in responses if r['success']]
if len(successful) < 2:
    print("Warning: Low response rate, consider retrying")

# Check for contradictions
# Implement your validation logic
```

### 3. Cost Management

```python
# Monitor token usage
total_tokens = sum(len(r['content']) for r in responses if r['success'])
estimated_cost = total_tokens * 0.00003  # Example rate

print(f"Estimated cost: ${estimated_cost:.4f}")
```

### 4. Rate Limiting

```python
import asyncio

# Add delays between batches
for prompt_batch in batches:
    results = await bridge.consult_all_experts(prompt_batch)
    await asyncio.sleep(1)  # 1 second between batches
```

---

## Security Notes

⚠️ **CRITICAL SECURITY PRACTICES**:

1. **Never commit API keys**
   ```bash
   # Add to .gitignore
   echo "api_config.json" >> .gitignore
   echo "consultation_log_*.json" >> .gitignore
   ```

2. **Use environment variables** (alternative to config file)
   ```python
   import os

   config = {
       "api_keys": {
           "grok": os.getenv('GROK_API_KEY'),
           "chatgpt": os.getenv('OPENAI_API_KEY'),
           "gemini": os.getenv('GEMINI_API_KEY')
       }
   }
   ```

3. **Rotate keys regularly**
   - Generate new keys monthly
   - Revoke old keys immediately if compromised

4. **Monitor usage**
   - Set up billing alerts
   - Review API logs for unusual activity

---

## Extending the Framework

### Add New AI Models

```python
async def query_claude(self, prompt: str) -> Dict[str, Any]:
    """Add Claude API support"""
    headers = {
        "x-api-key": self.config['api_keys']['claude'],
        "anthropic-version": "2023-06-01",
        "content-type": "application/json"
    }

    payload = {
        "model": "claude-3-5-sonnet-20241022",
        "max_tokens": 4000,
        "messages": [{"role": "user", "content": prompt}]
    }

    async with aiohttp.ClientSession() as session:
        async with session.post(
            "https://api.anthropic.com/v1/messages",
            headers=headers,
            json=payload
        ) as response:
            # Handle response
            pass
```

### Custom Analysis

```python
def analyze_consensus(self, responses):
    """Determine if experts agree"""
    contents = [r['content'] for r in responses if r['success']]

    # Simple similarity check
    if len(contents) < 2:
        return {"consensus": False, "reason": "Insufficient responses"}

    # Implement similarity algorithm
    # Return consensus analysis
```

---

## License

This framework is provided as-is for educational and development purposes. Developed as part of the Physical Logic Framework project.

**Original Context**: Formal verification in Lean 4 for Logic Field Theory
**Generalized For**: Any domain requiring multi-model AI consultation

---

## Support & Community

**Questions?**
- Check troubleshooting section above
- Review example projects
- Test with `test_suite.py`

**Contributing**:
- Customize for your domain
- Share your validation patterns
- Document your use cases

**Credits**:
- Original development: Physical Logic Framework project
- Author: James D. Longmire
- Framework: Multi-LLM consultation system

---

## Version History

**v1.0** (2025-10-03)
- Initial standalone release
- 3-model support (Grok, ChatGPT, Gemini)
- Parallel consultation
- Response synthesis
- Domain validation framework
- Comprehensive test suite

---

## Quick Reference

**Common Commands**:
```bash
# Setup
cp api_config_template.json api_config.json
# Edit api_config.json with your keys

# Test
python test_suite.py

# Use
python -c "import asyncio; from claude_llm_bridge import MultiLLMBridge; asyncio.run(MultiLLMBridge().consult_all_experts('test'))"
```

**File Structure**:
```
multi_LLM_model/
├── README.md                   # This file
├── claude_llm_bridge.py        # Core framework
├── test_suite.py               # Testing framework
├── api_config_template.json    # Configuration template
└── api_config.json            # Your config (create this, never commit!)
```

---

**Ready to get started? Follow the Quick Start section above!** 🚀
