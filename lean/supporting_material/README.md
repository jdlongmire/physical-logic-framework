# Supporting Material - Lean 4 Proof Development

**Date**: October 2025
**Purpose**: Research notes, planning documents, and test files for Lean 4 formalization

---

## Contents (8 files)

### 1. Amplitude Hypothesis Research (2 files)

**AMPLITUDE_HYPOTHESIS_PROOF_SKETCH.md** (~13 KB)
- Proof sketch for amplitude hypothesis formalization
- MaxEnt derivation in Lean 4
- Strategy for deriving |a_σ|² = 1/|V_K| from Shannon entropy

**AMPLITUDE_HYPOTHESIS_RESEARCH_NOTES.md** (~18 KB)
- Comprehensive research notes on amplitude hypothesis
- Literature review and mathematical framework
- Connection to Born rule derivation

### 2. MaxEnt Formalization (1 file)

**MAXENT_FORMALIZATION_PLAN.md** (~8 KB)
- Plan for formalizing maximum entropy theorem in Lean 4
- Strategy for proving P(σ) = 1/|V_K| uniquely maximizes Shannon entropy
- Connection to Kullback-Leibler divergence

### 3. State Space Enumeration (2 files)

**S4_ENUMERATION_PLAN.md** (~3.5 KB)
- Plan for enumerating S_4 valid states in Lean 4
- Strategy for proving |V_2| = 9 for N=4, K=2
- Extends S_3 enumeration approach

**s3_enum_strategy.lean** (~2 KB)
- Test strategy file for S_3 enumeration
- Helper tactics and approaches
- Prototype code for verification

### 4. Bug Fixes & Corrections (1 file)

**VALIDITY_ARRANG_FIX.md** (~3 KB)
- Documentation of validity arrangement fix
- Corrects issues in proof structure
- Ensures consistency across theorems

### 5. Statistics & Testing (2 files)

**PROOF_STATISTICS.md** (~8 KB)
- Statistics on Lean 4 formalization progress
- Line counts, theorem counts, verification status
- ~82% framework verified (as of October 2025)

**test_visibility.lean** (~100 bytes)
- Simple visibility test file
- Checks Lean 4 import and compilation

---

## Status

**Lean 4 Formalization**: ~82% complete

**Verified Components**:
- ✅ MaxEnt theorem (Born rule from Shannon entropy)
- ✅ S_3 complete enumeration (|V_1| = 3)
- ✅ S_4 complete enumeration (|V_2| = 9)
- ✅ L-flow monotonicity properties
- ⏳ Amplitude hypothesis (in progress)

---

## Actual Proof Files

**Location**: `../LFT_Proofs/PhysicalLogicFramework/`

**Main modules**:
- `Foundations/` - Core definitions and axioms
- `LogicField/` - L-flow and constraint theory
- `QuantumEmergence/` - Born rule and quantum structure

---

## Project Configuration

**Location**: `../` (parent folder)

**Files**:
- `lakefile.toml` - Lake build configuration
- `lake-manifest.json` - Dependency manifest
- `lean-toolchain` - Lean version specification
- `.lake/` - Build artifacts (auto-generated)

---

## Usage

These documents support Lean 4 proof development:

1. **Research notes**: Background and strategy for formalizations
2. **Planning docs**: Step-by-step formalization plans
3. **Test files**: Prototype code and visibility checks
4. **Statistics**: Track verification progress

**For proof development**: Reference planning documents before implementing new theorems in `LFT_Proofs/`.

**For status updates**: See PROOF_STATISTICS.md for current verification percentage.

---

## File Organization

**Main lean/ folder** (`../`):
- lakefile.toml, lake-manifest.json, lean-toolchain (project config)
- LFT_Proofs/ (actual proof files)
- supporting_material/ (this folder)

**This folder** (`supporting_material/`):
- Research notes and planning documents (6 .md files)
- Test/strategy files (2 .lean files)

**Clean structure for Lean 4 project** ✅
