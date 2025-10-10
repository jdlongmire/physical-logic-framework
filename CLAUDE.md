# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## 🚀 Session Startup Protocol

**When starting a new session, you will be asked to read this file (CLAUDE.md).**

**Upon reading CLAUDE.md, immediately read the latest session file in `Session_Log/`**

Find the most recent `Session_X.Y.md` file (highest X.Y number) in the `Session_Log/` directory. This file contains everything needed to resume:
- ✅ Complete session history and accomplishments
- 🎯 Current research focus and strategic direction
- 📊 Honest theory viability assessment
- 🗺️ Full systematic research roadmap
- 🔍 All files changed, commits made this session
- 🎬 Specific next tasks (with clear options)
- 📁 Guide to all key documents

**After reading the latest session file, you will have complete context and can continue work immediately.**

**Note**: Session_0.0.md is a historical snapshot and should not be updated.

---

## 🔍 Program Auditor Agent Protocol

**CRITICAL**: Before making ANY claims about project completion status, run the Program Auditor Agent critical review.

**Purpose**: Prevent overclaiming, hype, and disconnect between formal proofs and computational validation.

### When to Run Auditor

**Mandatory audit triggers**:
- ✅ At the start of each new session (after reading session log)
- ✅ Before making any public claims about completion status
- ✅ After completing any sprint or major milestone
- ✅ Monthly comprehensive audit
- ✅ Before updating README or documentation with completion statistics

### Quick Audit Checklist

**Lean Proof Status**:
```bash
# Count sorry statements by folder
echo "Foundations:"
grep -c sorry lean/LFT_Proofs/PhysicalLogicFramework/Foundations/*.lean 2>/dev/null || echo "0"
echo "LogicField:"
grep -c sorry lean/LFT_Proofs/PhysicalLogicFramework/LogicField/*.lean 2>/dev/null || echo "0"
echo "Dynamics:"
grep -c sorry lean/LFT_Proofs/PhysicalLogicFramework/Dynamics/*.lean 2>/dev/null || echo "0"
echo "QuantumEmergence:"
grep -c sorry lean/LFT_Proofs/PhysicalLogicFramework/QuantumEmergence/*.lean 2>/dev/null || echo "0"

# Verify builds
cd lean && lake build
```

**Completion Criteria**:
- ❌ **NOT complete** if file contains ANY `sorry` statements
- ❌ **NOT complete** if file fails to build (`lake build` errors)
- ❌ **NOT complete** if any imported dependency has `sorry` statements
- ✅ **Complete** ONLY if: 0 sorry + builds successfully + all dependencies complete

### Validation Rules (from Program_Auditor_Agent.md)

**Rule 1**: Stop using "complete," "validated," "finished" without verification
**Rule 2**: Cross-validate Lean proofs ↔ computational notebooks
**Rule 3**: Quantify with numbers, not qualitative statements
**Rule 4**: Start with what's wrong, not what works
**Rule 5**: Puncture hype with facts

### Red Flag Language

**DO NOT use without verification**:
- ❌ "complete" / "completed" / "finished"
- ❌ "validated" / "proven"
- ❌ "historic achievement" / "breakthrough"
- ❌ "X modules with 0 sorry" (without showing grep results)

**DO use**:
- ✅ "X sorry statements remain in module Y" (with grep evidence)
- ✅ "Module builds successfully (verified YYYY-MM-DD)"
- ✅ "Module has 0 sorry but depends on incomplete module Z"
- ✅ Conservative, verifiable claims with audit evidence

### Full Audit Protocol

For comprehensive audits, follow the complete protocol in `Program_Auditor_Agent.md`:
1. Lean Code Inventory (Phase 1)
2. Notebook Execution Audit (Phase 2)
3. Cross-Validation Matrix (Phase 3)
4. Empirical Testability (Phase 4)
5. Dependency Analysis (Phase 5)

**Generate audit report** using template in Program_Auditor_Agent.md

### Integration with Session Startup

**Updated Session Startup Protocol**:
1. Read CLAUDE.md (this file)
2. Read latest session file in `Session_Log/`
3. **Run quick audit checklist** (grep for sorry, verify latest build status)
4. **Update understanding** with audit results before making claims
5. Continue work with honest baseline

**Protection**: This ensures every session starts with verified facts, not assumptions.

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
1. Read: Latest Session_X.Y.md file in Session_Log/
2. Review: [Key documents from this session]
3. Continue: [Next major task]
```

### During Session: Progressive Updates

**CRITICAL**: Update session log progressively to protect against abrupt session interruption.

**Update trigger**: After completing each major phase/task

**How to update**:
1. Rename current file: `Session_X.Y.md` → `Session_X.(Y+1).md`
2. Update all sections with new progress
3. Add new phases as they complete
4. Update "Files Created/Modified" list
5. Note key achievements
6. **Commit and push** session log immediately after each update

**Progressive Update Protocol** (Protection Against Interruption):

✅ **DO** update session log in real-time:
- After each major task completion
- After each git commit
- After each notebook/file creation
- Before any long-running operations
- At natural breakpoints in work

❌ **DO NOT** wait until end of session to update

**Update Frequency**: Every 30-60 minutes of active work, or after each deliverable

**Example progression**:
- `Session_3.0.md` - Session start (Sprint 1 begins)
- `Session_3.1.md` - After claim moderation complete [COMMITTED & PUSHED]
- `Session_3.2.md` - After sensitivity analysis complete [COMMITTED & PUSHED]
- `Session_3.3.md` - After table addition complete (Sprint 1 done) [COMMITTED & PUSHED]

**Session Recovery**: If session ends abruptly, the most recent Session_X.Y.md provides complete recovery point.

### End of Session: Finalize

**Before ending session**:
1. ✅ Make final rename to highest Y value
2. ✅ Complete all sections in current session log (Session_X.Y.md)
3. ✅ Ensure session log includes updated status, viability, next steps
4. ✅ Archive any old/superseded session files to `archive/` if needed
5. ✅ Ensure `Session_Log/` contains:
   - Session_0.0.md (historical snapshot, do not modify)
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
2. ✅ Complete all sections in current session log (Session_X.Y.md)
3. ✅ Ensure session log includes updated status, viability, next steps
4. ✅ **Push all commits to GitHub** (`git push origin main`)
5. ✅ Archive any old/superseded session files to `archive/` if needed
6. ✅ Ensure `Session_Log/` contains:
   - Session_0.0.md (historical snapshot, do not modify)
   - Current and recent session logs (Session_X.Y.md format)
   - README.md

**Result**: All work is safely backed up on GitHub and available for collaboration/review.

---

## 📋 Sprint Documentation Protocol

**IMPORTANT**: Sprints are tracked in the `sprints/` folder with daily progress updates and team consultation logs.

### Sprint Folder Structure

```
sprints/
├── README.md                                    # Sprint overview and status
├── SPRINT_PLAN_ENHANCED_TEAM_INTEGRATION.md    # Master 10-week sprint plan
├── sprint_X/                                    # Individual sprint folders
    ├── SPRINT_X_TRACKING.md                    # Daily progress tracking
    ├── team_consultations/                     # Team consultation logs
    ├── notebooks/                              # Sprint-specific notebook outputs
    └── lean/                                   # Sprint-specific Lean development
```

### Starting a New Sprint

**When beginning a new sprint**:
1. ✅ Create sprint folder: `sprints/sprint_X/`
2. ✅ Initialize tracking document: `SPRINT_X_TRACKING.md` (see template in `sprints/README.md`)
3. ✅ Create subfolders: `team_consultations/`, `notebooks/`, `lean/`
4. ✅ Update `sprints/README.md`: Mark sprint as "In Progress" in status table
5. ✅ Update session log: Reference sprint start in `Session_Log/Session_X.Y.md`
6. ✅ Update todo list: Add sprint deliverables as trackable tasks
7. ✅ Commit and push: Initial sprint setup

### During Sprint (Daily Updates)

**CRITICAL**: Update sprint tracking document daily to protect against session interruption.

**Daily workflow**:
1. ✅ Add daily log entry to `SPRINT_X_TRACKING.md` with:
   - Notebook track progress
   - Lean track progress
   - Team track consultations and quality scores
   - Integration notes (how tracks informed each other)
2. ✅ Save team consultations: Store in `sprint_X/team_consultations/` with date stamps
3. ✅ Update deliverables checklist: Mark items as in progress or complete
4. ✅ Commit regularly: Push progress at end of each day or major milestone
5. ✅ Cross-reference: Update both sprint tracking and session log

**Team consultation workflow**:
1. Run consultation via multi-LLM bridge
2. Save results to `sprint_X/team_consultations/consultation_X_YYYYMMDD.txt` and `.json`
3. Document in tracking file with quality score
4. Apply insights to current development
5. Ensure quality score >0.70 for sprint success metrics

### Completing a Sprint

**Before marking sprint complete**:
1. ✅ Finalize tracking document: Mark all deliverables as complete with final status
2. ✅ Sprint review: Conduct comprehensive team review and document results
3. ✅ Update `sprints/README.md`: Mark sprint as "Complete" with completion date
4. ✅ Archive outputs: Ensure all notebooks, Lean files, and consultations are saved
5. ✅ Update master plan: Mark sprint complete in `SPRINT_PLAN_ENHANCED_TEAM_INTEGRATION.md`
6. ✅ Session log: Document sprint completion with full accomplishments
7. ✅ Next sprint handoff: Document what's ready, open questions, recommendations
8. ✅ Commit and push: Final sprint state

### Sprint Success Metrics

**Per Sprint**:
- All team consultations score >0.70 average
- 0 `sorry` statements in Lean modules
- 100% computational validation in notebooks
- Daily integration maintained across all three tracks
- Sprint review: Team consensus "Accept" or "Minor Revision"

**Overall Program (All Sprints Complete)**:
- All critical peer review issues addressed
- Complete Lean package (~1,500 lines, fully verified)
- New notebooks (~30,000 words) validated
- Paper ready for submission
- Final team review: "Accept" or "Minor Revision" from all 3 LLMs

### Integration with Session Logs

Sprint tracking complements session logs:

- **Session Logs** (`Session_Log/`): Overall session progress, git commits, file changes, cross-session continuity
- **Sprint Tracking** (`sprints/sprint_X/`): Detailed daily sprint-specific work, team consultations, deliverable status

**Cross-referencing**:
- Session logs should reference active sprint
- Sprint tracking should note which session(s) contain the work
- Both should be updated progressively throughout the day

### Team Consultation Budget

**Total Available**: 61 consultations over 10 weeks (Sprints 6-10)
**Actual API Calls**: ~40-45 (due to 50% cache hit rate)

**Consultation allocation per sprint** (see master plan for details):
- Sprint 6: 13 consultations
- Sprint 7: 15 consultations
- Sprint 8: 10 consultations
- Sprint 9: 14 consultations
- Sprint 10: 9 consultations

**Quality requirements**:
- Each consultation must be documented with quality score
- Average consultation quality >0.70 required for sprint success
- Failed consultations (quality <0.50) should be re-run with refined prompts

---

## 👤 Author Information

**Author**: James D. (JD) Longmire
**Affiliation**: Northrop Grumman Fellow (unaffiliated research)
**ORCID**: [0009-0009-1383-7698](https://orcid.org/0009-0009-1383-7698)

**IMPORTANT**: All notebooks, papers, and documentation must include proper attribution.

### Notebook Copyright Format

**All Jupyter notebooks** must use this exact copyright block (3 lines, clean format):

```markdown
**Copyright © 2025 James D. (JD) Longmire**
**License**: Apache License 2.0
**Citation**: Longmire, J.D. (2025). *Logic Field Theory: Deriving Quantum Mechanics from Logical Consistency*. Physical Logic Framework Repository.
```

**DO NOT use**:
- ❌ Any other author name (e.g., "Jesse Lonquist")
- ❌ Any other license (e.g., "MIT License")
- ❌ Multi-line author blocks with separate fields
- ❌ Excessive formatting or bold headers

**Correct placement**: In first markdown cell, after title and subtitle, before "Purpose" section.

**Professional tone**: Notebooks must maintain a professional, scholarly tone throughout:
- ❌ NO informal thinking commentary ("Wait, that doesn't seem right...")
- ❌ NO self-correction notes ("Let me recalculate...", "Actually, this is wrong...")
- ❌ NO stream-of-consciousness ("Hmm, let me think about this...")
- ✅ Present the correct approach directly and professionally
- ✅ If multiple approaches exist, present them as alternatives, not as corrections

See Notebook 08 (`notebooks/Logic_Realism/08_Energy_Level_Structure.ipynb`) for reference template.

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
├── multi_LLM/              # AI consultation (public)
│   ├── consultation/       # Team consultation results
│   └── enhanced_llm_bridge.py  # Multi-LLM system
├── sprints/                # Sprint planning and tracking
│   ├── sprint_6/           # Current sprint (Born Rule)
│   └── SPRINT_PLAN_ENHANCED_TEAM_INTEGRATION.md
├── scripts/                # Analysis utilities
├── Session_Log/            # Session tracking (X.Y format)
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

**Important**: After each session, ensure the current session log (Session_X.Y.md) is complete with updated status, accomplishments, viability assessments, and next steps. Also update relevant README files as needed.
- keep hyperbole to a minimum
- always keep the tone professional
- track sprints in the sprints root folder
- validate all claims tied to amount of sorrys in Lean proofs
- validate all notebooks, Lean proofs, code, etc with the multi-LLM team