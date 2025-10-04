# Research & Data

This directory contains research artifacts, session summaries, and data generated during LFT development.

## Contents

### `amplitude_hypothesis_breakthrough/` (2025-01-04)

Major theoretical breakthrough session artifacts:
- **AMPLITUDE_BREAKTHROUGH_SUMMARY.md**: Session summary of amplitude hypothesis proof discovery
- **PROOF_VALIDATED_SUMMARY.md**: Final status after self-validation (85% confidence)
- **VALIDATION_REQUIRED.md**: Validation framework document

**What was achieved**: Proof that amplitude distribution follows from maximum entropy principle
- Built on Caticha's entropic dynamics framework (2000, 2019)
- Derived P(σ) = 1/|V| for h(σ) ≤ K(N)
- Verified for N=3 (P=1/3) and N=4 (P=1/9)
- Closed critical theoretical gap in LFT

**Key documents** (elsewhere in repo):
- Full proof: `paper/supplementary/amplitude_hypothesis_proof.md` (58KB)
- Proof sketch: `lean/AMPLITUDE_HYPOTHESIS_PROOF_SKETCH.md` (40KB)
- Literature review: `lean/AMPLITUDE_HYPOTHESIS_RESEARCH_NOTES.md`
- Validation: `multi_LLM_model/validation_results/self_validation_claude.md`

### `paper_development/` (2025-01-03)

Paper revision process artifacts from Tier 1 critical revisions:

**Subdirectories**:
- `consultations/`: Multi-LLM expert consultations (Born rule, I2PS, spacetime)
- `revision_plans/`: Revision plans based on expert feedback (Gemini analyses)
- `peer_review/`: Mock peer review materials and readiness assessment

**Key achievements**:
- Rigorous I2PS formalization (∏ Sₙ with measure theory)
- Honest Born rule framing (verified cases, not general derivation)
- Honest spacetime framing (research program with identified challenges)
- Amplitude hypothesis identified as critical gap (later proven!)

**Old versions**:
- It_from_Logic_Scholarly_Paper_PRE_RESTRUCTURE.md (before Tier 1 revisions)
- CONDENSED_Section7.md (condensed version of Section 7)

See `paper_development/README.md` for detailed documentation.

## Organization

This directory is for:
- Session breakthrough summaries
- Research investigation artifacts
- Computational data and results
- Temporary research documents

**Not** for:
- Source code (see `lean/`, `scripts/`, `multi_LLM_model/`)
- Papers (see `paper/`)
- Notebooks (see `notebooks/`)
- Documentation (see root-level .md files like SESSION_STATUS.md, CLAUDE.md)

## History

- 2025-01-04: Created as research_and_data (renamed from data)
- 2025-01-04: Added amplitude_hypothesis_breakthrough artifacts
- 2025-01-04: Moved paper development artifacts from paper/ folder
  - Consultations, revision plans, peer review materials
  - Old paper versions and condensed sections
  - Cleaned paper/ to contain only main paper and appendices
