# Sprint 8 Quick Reference

**Purpose**: Integrate Sprint 7 measurement work into Logic_Realism canonical suite

---

## The Simple Story

1. **Sprint 7 created good content in the wrong place** (approach_1 folder)
2. **Logic_Realism is missing critical pieces** (Schrödinger equation, measurement theory)
3. **Sprint 8 fixes this** by moving content and renumbering everything to be sequential

---

## What Gets Moved

**From approach_1 (to be deprecated) → To Logic_Realism:**

| Source | → | Target |
|--------|---|--------|
| approach_1/15_Schrodinger_From_Fisher_Metric.ipynb | → | Logic_Realism/06_Schrodinger_From_Fisher_Metric.ipynb |
| approach_1/16_Measurement_Mechanism.ipynb | → | Logic_Realism/07_Measurement_Constraint_Addition.ipynb |
| approach_1/17_Observer_Decoherence.ipynb | → | Logic_Realism/08_Observer_Decoherence.ipynb |
| approach_1/18_Toy_Model_Measurement.ipynb | → | Logic_Realism/09_Toy_Model_Measurement_Cycle.ipynb |

---

## What Gets Renumbered

**Existing Logic_Realism notebooks shift up by 4:**

| Old | → | New | Title |
|-----|---|-----|-------|
| 06 | → | 10 | Interferometry and Mach-Zehnder |
| 07 | → | 11 | Qubit Systems and Bloch Sphere |
| 08 | → | 12 | Energy Level Structure |
| 09 | → | 13 | Finite-N Quantum Corrections |
| 10 | → | 14 | Spectral Mode Analysis |
| 11 | → | 15 | Entropy Saturation |
| 12 | → | 16 | Unitary Invariance Foundations |
| 13 | → | 17 | Constraint Parameter Foundation |

---

## Lean Files to Update

**3 files need notebook reference updates:**

1. **BornRuleNonCircularity.lean**
   - Change: "Notebook 12" → "Notebook 16"
   - Change: "Notebook 13" → "Notebook 17"
   - (14 occurrences total)

2. **QuantumDynamics.lean**
   - Change: "Notebook 15" → "Notebook 06"

3. **MeasurementMechanism.lean**
   - Change: "Notebooks 16-18" → "Notebooks 07-09"

---

## Final Structure

**Logic_Realism (18 notebooks total):**

```
00-05: Foundation (unchanged)
  00: Permutations and Inversions
  01: Logical Operators
  02: Constraint Threshold
  03: Maximum Entropy to Born Rule
  04: Fisher Information Metric
  05: Lagrangian-Hamiltonian Duality

06-09: Dynamics & Measurement (NEW from approach_1)
  06: Schrödinger from Fisher Metric
  07: Measurement as Constraint Addition
  08: Observer & Decoherence
  09: Toy Model Measurement Cycle

10-12: Physical Systems (renumbered from 06-08)
  10: Interferometry and Mach-Zehnder
  11: Qubit Systems and Bloch Sphere
  12: Energy Level Structure

13-15: Experimental Predictions (renumbered from 09-11)
  13: Finite-N Quantum Corrections
  14: Spectral Mode Analysis
  15: Entropy Saturation

16-17: Advanced Topics (renumbered from 12-13)
  16: Unitary Invariance Foundations
  17: Constraint Parameter Foundation
```

---

## Folder Changes

**Before:**
```
notebooks/
├── approach_1/           # Active development, mixed content
├── Logic_Realism/        # 14 notebooks (00-13)
```

**After:**
```
notebooks/
├── approach_1_deprecated/   # DEPRECATED (renamed, historical only)
├── Logic_Realism/           # 18 notebooks (00-17) - CANONICAL
```

---

## Timeline

**Estimated Duration**: 12-16 hours (2-3 days)

**Phases**:
1. Preparation (1h) - Setup, backup, analysis
2. Migration (4-6h) - Adapt 4 notebooks to V2 architecture
3. Renumbering (2-3h) - Rename 8 existing notebooks
4. Lean Updates (1-2h) - Update 3 Lean files
5. Documentation (2h) - Update README files, create deprecation notice
6. Validation (2h) - Test all notebooks, Lean builds, cross-references

---

## Key Risks & Mitigations

**Risk**: File collision during renumbering (e.g., renaming 06→10 when 10 exists)
**Mitigation**: Rename in reverse order (13→17, 12→16, ..., 06→10)

**Risk**: Lean builds fail after reference updates
**Mitigation**: Update and test one file at a time, lake build after each

**Risk**: Cross-references break
**Mitigation**: Search entire codebase for "Notebook XX", validate systematically

---

## Why This Matters

**Pedagogical Flow**: Can't teach interferometry (10) without first deriving how states evolve (06)

**Single Source of Truth**: Eliminates confusion between approach_1 and Logic_Realism

**Peer Review**: Addresses Issue #2 (measurement underdeveloped) in the canonical location

**Lean Integration**: All formal proofs reference the same, consistent notebook suite

---

## Post-Sprint Outcome

✅ One canonical notebook suite (Logic_Realism, 18 notebooks)
✅ Proper pedagogical flow (Foundation → Dynamics → Measurement → Applications)
✅ All Lean proofs consistent with notebook numbering
✅ approach_1 deprecated, no fragmentation

**Ready to address Peer Review Issue #2 with concrete evidence from notebooks 07-09.**

---

**See full details in**: `sprints/SPRINT_8_PLAN.md`
