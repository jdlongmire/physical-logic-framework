# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## 🚀 Session Startup Protocol

**When starting a new session, you will be asked to read this file (CLAUDE.md).**

**Upon reading CLAUDE.md, immediately read**: [`Session_Log/Session_0.0.md`](Session_Log/Session_0.0.md)

`Session_Log/Session_0.0.md` is the master status file containing everything needed to resume:
- ✅ Complete session history and accomplishments
- 🎯 Current research focus and strategic direction
- 📊 Honest theory viability assessment
- 🗺️ Full systematic research roadmap (Year 1-2)
- 🔍 All files changed, commits made this session
- 🎬 Specific next tasks (with clear options)
- 📁 Guide to all key documents

**After reading Session_Log/Session_0.0.md, you will have complete context and can continue work immediately.**

---

## 📝 Session Logging Protocol

**IMPORTANT**: Sessions are tracked by sequential count, with progressive updates during active work.

### Creating New Session Log

**Format**: `Session_Log/Session_X.Y.md`
- **X** = Session number (increments with each new session)
- **Y** = Update number within session (starts at 0, increments as work progresses)

**Examples**:
- `Session_Log/Session_3.0.md` (new session starts)
- `Session_Log/Session_3.1.md` (first major update)
- `Session_Log/Session_3.2.md` (second major update)
- `Session_Log/Session_3.3.md` (final update before completion)

**When to create**:
- ✅ At the start of each new work session: Create `Session_X.0.md`
- ✅ After completing major tasks/phases: Rename to `Session_X.Y.md` (increment Y)
- ✅ Progressive updates capture evolving work in real-time
- ❌ Do NOT create multiple files - rename the same file with incremented Y

**Template structure**:
```markdown
# Session X.Y - [Brief Description]

**Session Number**: X.Y
**Started**: [Timestamp if known]
**Focus**: [Research / Paper / Lean / Review / Organization]

---

## Session Overview

[Brief summary of goals and current progress]

---

## Phase 1: [Name]

### Accomplishments
1. [Item 1]
2. [Item 2]

### Files Created/Modified
- [File 1]
- [File 2]

---

## Files Created/Modified (Total: [count])

### Created
- [New files]

### Modified
- [Modified files]

---

## Key Achievements

[Major milestones reached this session]

---

## Next Steps

**To Resume**:
1. Read: Session_Log/Session_0.0.md
2. Review: [Key documents from this session]
3. Continue: [Next major task]
```

### During Session: Progressive Updates

**Update trigger**: After completing each major phase/task

**How to update**:
1. Rename current file: `Session_X.Y.md` → `Session_X.(Y+1).md`
2. Update all sections with new progress
3. Add new phases as they complete
4. Update "Files Created/Modified" list
5. Note key achievements

**Example progression**:
- `Session_3.0.md` - Session start (Sprint 1 begins)
- `Session_3.1.md` - After claim moderation complete
- `Session_3.2.md` - After sensitivity analysis complete
- `Session_3.3.md` - After table addition complete (Sprint 1 done)

### End of Session: Finalize

**Before ending session**:
1. ✅ Make final rename to highest Y value
2. ✅ Complete all sections in session log
3. ✅ Update `Session_Log/Session_0.0.md` with latest status
4. ✅ Archive any old/superseded session files to `archive/` if needed
5. ✅ Ensure `Session_Log/` contains only:
   - Session_0.0.md (master status file)
   - Current and recent session logs (Session_X.Y.md format)
   - README.md

**Result**: Sequential, versioned session history with clear progression

### Retroactive Numbering

**Previous date-based sessions** map to new numbering:
- `SESSION_2025_10_05_COMPLETE.md` = Session 1.0 (retroactive)
- `SESSION_2025_10_06_COMPLETE.md` = Session 2.0 (retroactive)
- Current session = Session 3.0 (new format begins)

---

## 🔄 Git Synchronization Protocol

**IMPORTANT**: Keep the remote repository synchronized to ensure work is backed up and accessible.

### When to Push to Remote

**Push commits to GitHub**:
- ✅ After completing major phases/milestones (every Session_X.Y update)
- ✅ Before ending a work session (final safety backup)
- ✅ After significant breakthroughs or research results
- ✅ When session log indicates completion of substantial work

### Standard Push Command

```bash
git push origin main
```

### Verification Steps

1. **Check sync status**: `git log origin/main..HEAD --oneline`
   - If output shows commits, they need to be pushed

2. **Push to remote**: `git push origin main`

3. **Verify on GitHub**: Check the repository to confirm latest commits are visible

### Integration with Session Workflow

**Updated "End of Session: Finalize" checklist**:
1. ✅ Make final rename to highest Y value
2. ✅ Complete all sections in session log
3. ✅ Update `Session_Log/Session_0.0.md` with latest status
4. ✅ **Push all commits to GitHub** (`git push origin main`)
5. ✅ Archive any old/superseded session files to `archive/` if needed
6. ✅ Ensure `Session_Log/` contains only:
   - Session_0.0.md (master status file)
   - Current and recent session logs (Session_X.Y.md format)
   - README.md

**Result**: All work is safely backed up on GitHub and available for collaboration/review.

---

## Repository Overview

This is the **Physical Logic Framework (PLF)** repository, containing mathematical derivations and computational simulations for Logic Field Theory (LFT) - a theoretical physics framework that proposes physical reality emerges from logical filtering of information: **A = L(I)**.

## Architecture

### Core Components

1. **Publications** (`paper/`): Canonical scholarly papers and supplementary materials
   - **Main Paper**: `It_from_Logic_Scholarly_Paper.md` (peer-review ready)
   - **Figures**: Publication-ready visualizations (figure1-6)
   - **Supplementary**: Foundational framework, first-principles derivation, Gödel argument
   - This is the primary reference for the theoretical framework

2. **Jupyter Notebooks** (`notebooks/approach_1/`): Computational validation and exploration
   - **Foundation Layer** (00-02): Core thesis, information space, and logical operator implementation
   - **Worked Examples** (03-05): Complete analyses for N=3,4 with geometric visualizations
   - **Spacetime Emergence** (06-09): Scaling analysis, time emergence, and strain dynamics
   - **Quantum Derivations** (10-13): Quantum mechanics derivation from geometric principles
   - **Extensions** (14, 20-22): Gravity proof-of-concept, predictions, and comparative analysis

3. **Lean 4 Proofs** (`lean/LFT_Proofs/`): Formal mathematical verification
   - Configured with Mathlib for advanced mathematical libraries
   - Project name: `PhysicalLogicFramework`
   - Modules: Foundations, LogicField, QuantumEmergence

4. **Multi-LLM System** (`multi_LLM_model/`): AI consultation framework
   - Public distribution package for multi-model expert consultation
   - Used in development for Lean 4 proof assistance
   - Parallel queries to Grok-3, GPT-4, Gemini-2.0

5. **Analysis Scripts** (`scripts/`): Computational utilities
   - Constraint analysis and validation tools
   - Data processing scripts

6. **Archive** (`archive/`): Historical development artifacts
   - Previous paper versions (v1-v5)
   - AI conversation logs and development notes
   - Session artifacts

### Key Mathematical Concepts

- **Information Space**: Directed graphs on N elements
- **Logical Operator L**: Composition of Identity, Non-Contradiction, and Excluded Middle
- **Permutohedron**: The N-1 dimensional geometric realization of the symmetric group S_N
- **L-Flow**: Monotonic descent process that generates the arrow of time

## Development Commands

### Python/Jupyter Environment

```bash
# Install Python dependencies
pip install -r notebooks/LFT_requirements.txt

# Launch Jupyter notebook environment
jupyter notebook

# Navigate to notebooks/ directory and run foundation notebooks first (00-02)
```

### Core Dependencies
- `numpy>=1.20.0` - Numerical computation
- `matplotlib>=3.4.0` - Plotting and visualization  
- `networkx>=2.6.0` - Graph algorithms
- `pandas>=1.3.0` - Data manipulation
- `scipy>=1.7.0` - Scientific computing
- `jupyter>=1.0.0` - Notebook environment

### Lean 4 Formal Proofs

```bash
# Build Lean project (requires Lean 4 and Lake)
cd lean
lake build

# Check specific proof files
lake exe cache get  # Download mathlib cache
lean --make LFT_Proofs/
```

Note: Lean/Lake may not be available in all environments. The repository can be used without Lean for computational work.

## Computational Parameters

### Safe Operating Ranges
- **N (elements)**: 3-6 for exact computation, 3-8 for sampling methods
- **K (micro-constraints)**: 1-200 for finite-K quantum effects
- **trials**: 1000-10000 for statistical convergence

### Memory Requirements
- N≤4: Any modern laptop
- N=5: ~1GB RAM  
- N=6: ~4GB RAM
- Full analysis: ~30 minutes runtime

## Common Workflows

### 1. Quick Validation
Run notebooks 03 (N=3 example) and 04 (N=4 geometry) to verify core constructions work correctly.

### 2. Full Reproduction
Execute notebooks in order: Foundation (00-02) → Examples (03-05) → Choose specialization track (quantum 10-13, spacetime 06-09, or predictions 20-22).

### 3. New Research
Start with Foundation notebooks to understand the framework, then modify parameters in existing notebooks or create new analyses.

## File Organization

### Repository Structure
```
physical_logic_framework/
├── paper/                   # Canonical publications
│   ├── It_from_Logic_Scholarly_Paper.md/pdf
│   ├── figures/            # Publication figures
│   ├── supplementary/      # Supporting documents
│   └── potential_extensions/ # Speculative future research
├── notebooks/              # Computational validation
│   └── approach_1/         # Complete theory (00-22)
├── lean/                   # Formal proofs
│   └── LFT_Proofs/PhysicalLogicFramework/
├── multi_LLM_model/        # AI consultation (public)
├── scripts/                # Analysis utilities
└── archive/                # Historical versions
```

### Notebook Outputs
Notebooks generate files in `notebooks/approach_1/outputs/`:
- `N*_permutohedron_*.png` - Geometric visualizations
- `N*_edge_distortions.csv` - Embedding quality metrics
- `finiteK_*.png` - Quantum finite-size effects
- `*_summary.json` - Numerical results

### Publication Figures
Canonical figures are in `paper/figures/`:
- 6 publication-ready PNG files (figure1-6)
- `figure_data.json` - Source data
- `figure_specifications.md` - Technical specs

### Key Verification Tests
```python
# Core construction (notebook 03)
N = 3
assert factorial(N) == 6  # S_3 has 6 elements
assert N*(N-1)*factorial(N)//2 == 6  # Adjacent edges

# Dimensionality (notebook 04)  
N = 4
assert N - 1 == 3  # Spatial dimensions

# Reproducibility - always set seeds
import numpy as np, random
np.random.seed(42); random.seed(42)
```

## Troubleshooting

- **Memory errors for N>6**: Use sampling methods or reduce trial counts
- **Missing outputs directory**: Notebooks create this automatically with `os.makedirs('./outputs', exist_ok=True)`
- **NetworkX version issues**: Ensure v2.6+ for `nx.all_topological_sorts()`
- **Slow linear extensions**: Add `limit=1000` parameter to enumeration functions

## Research Context

This repository implements active theoretical research in fundamental physics. All results are mathematical/computational demonstrations of the LFT framework. The core thesis is that physical laws (quantum mechanics, spacetime geometry, gravity) can be derived rather than postulated, emerging from logical consistency requirements on an information space.

**Important**: After each session make sure to update `Session_Log/Session_0.0.md` (master status file) and all relevant README files.