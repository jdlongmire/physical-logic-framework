# DEPRECATED: approach_1 Notebook Suite

**Status**: DEPRECATED as of October 10, 2025 (Sprint 8)

**Replacement**: `notebooks/Logic_Realism/` - Canonical notebook suite

---

## Why Deprecated?

This folder contained a parallel notebook suite that created fragmentation with the canonical `Logic_Realism/` suite. As of Sprint 8, all active notebook development uses `Logic_Realism/` as the single source of truth.

## What Was Migrated?

The following notebooks from this folder were migrated to `Logic_Realism/` with new numbering:

| Old (approach_1_deprecated) | New (Logic_Realism) | Title |
|---|---|---|
| 15 | 06 | Schrödinger Equation from Fisher Metric |
| 16 | 07 | Measurement as Constraint Addition |
| 17 | 08 | Observer & Decoherence |
| 18 | 09 | Toy Model: Full Measurement Cycle |

## Current Canonical Suite

All notebook work now uses `notebooks/Logic_Realism/` which contains:
- **18 sequential notebooks** (00-17)
- **V2 architecture** (3-line copyright, self-contained code, professional tone)
- **100% computational validation**
- **Lean proof integration** (all Lean proofs reference Logic_Realism notebooks)

## Historical Value

This folder is retained for historical reference only:
- Shows evolution of notebook development (Sprint 1-7)
- Contains earlier versions and experimental work
- Provides audit trail for computational validation

**DO NOT**:
- ❌ Reference these notebooks in papers or documentation
- ❌ Create new notebooks in this folder
- ❌ Use these notebooks for computational validation

**DO**:
- ✅ Use `notebooks/Logic_Realism/` for all notebook work
- ✅ Reference Logic_Realism notebooks in papers and Lean proofs
- ✅ Keep this folder for historical reference only

---

**Deprecated**: October 10, 2025
**Sprint**: 8 (Integration & Renumbering)
**See**: `Session_Log/Session_7.3.md` for full migration details
