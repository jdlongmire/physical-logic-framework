# Computational Notebooks - Logic Field Theory Research

**Author**: James D. (JD) Longmire
**Affiliation**: Northrop Grumman Fellow (unaffiliated research)
**ORCID**: [0009-0009-1383-7698](https://orcid.org/0009-0009-1383-7698)

## Overview

This directory contains computational validation and exploration for the Physical Logic Framework research program, comprising two theoretical approaches:
1. **Logic Realism** - V2 production notebooks (00-13) with complete mathematical exposition
2. **Logic Field Theory** - Original validation series (approach_1/, notebooks 00-22)

## Repository Organization

### Logic_Realism/ - Production Series (V2 Architecture) ⭐ RECOMMENDED

**Status**: 14 production notebooks (~37,000 words LaTeX proofs)
**Architecture**: Professional scholarly exposition with inline computational validation
**Coverage**: Foundation → Core Theorems → Physical Systems → Experimental Predictions

#### Foundation Layer (00-02)
| Notebook | Purpose | Key Result |
|----------|---------|------------|
| **00_Permutations_and_Inversions** | Permutohedron geometry, inversions metric | S_N structure, Cayley graphs |
| **01_Logical_Operators** | L-flow dynamics, arrow of time | Time emergence from logic |
| **02_Constraint_Threshold** | K(N) = N-2 triple proof | Mahonian, Coxeter, MaxEnt convergence |

#### Core Theorems (03-05)
| Notebook | Purpose | Key Result |
|----------|---------|------------|
| **03_Maximum_Entropy_to_Born_Rule** | MaxEnt → quantum probabilities | P = \|a\|² from first principles |
| **04_Fisher_Information_Metric** | Fisher metric = Fubini-Study | Information geometry = quantum geometry |
| **05_Lagrangian_Hamiltonian_Duality** | Minimal action ≡ minimal Fisher info | H = D - A (graph Laplacian) |

#### Physical Systems (06-08)
| Notebook | Purpose | Key Result |
|----------|---------|------------|
| **06_Interferometry_Mach_Zehnder** | Quantum interference from graphs | Phase shifts from permutohedron paths |
| **07_Qubit_Systems_Bloch_Sphere** | Qubit emergence | 2-level systems from S_N subsystems |
| **08_Energy_Level_Structure** | Energy quantization | Discrete levels from graph spectrum |

#### Experimental Predictions (09-11)
| Notebook | Purpose | Key Result |
|----------|---------|------------|
| **09_Finite_N_Quantum_Corrections** | Measurable QM deviations | 5 testable effects at ~10^{-8} precision |
| **10_Spectral_Mode_Analysis** | Statistical signatures | Semi-Poisson level spacing |
| **11_Entropy_Saturation** | Thermalization & Page curve | ETH emergence from constraints |

#### Born Rule Non-Circularity (12-13) - NEW
| Notebook | Purpose | Key Result |
|----------|---------|------------|
| **12_Unitary_Invariance_Foundations** | Unitarity from combinatorics | No quantum assumptions |
| **13_Constraint_Parameter_Foundation** | K(N)=N-2 validation | Information-theoretic foundation |

**Quality Standards**:
- ✅ Professional scholarly tone (no informal commentary)
- ✅ Copyright attribution (Apache 2.0 license)
- ✅ All code cells execute successfully
- ✅ Results match theoretical predictions (100% validation)
- ✅ Publication-quality figures (300 DPI)

**Documentation**: See `Logic_Realism/NOTEBOOK_STATUS.md` for comprehensive status report

### approach_1/ - Historical Validation Series

**Status**: 18 notebooks (complete computational exploration)
**Purpose**: Original constraint counting methodology with extensive parameter exploration
**Architecture**: Exploratory notebooks with detailed geometric visualizations

#### Key Notebooks
- **00-02**: Foundation (core thesis, information space, logical operators)
- **03-05**: Worked examples (N=3,4 complete analyses)
- **06-09**: Spacetime emergence (scaling, time, strain dynamics)
- **10-13**: Quantum derivations (Born rule, Tsirelson bound)
- **14**: Gravity proof-of-concept
- **20-22**: Extensions (predictions, comparative analysis)

**Status**: Complete V&V (validation & verification), enhanced with I2PS integration

## Prerequisites

### Required Libraries
```bash
pip install -r LFT_requirements.txt
```

Core dependencies:
```python
numpy >= 1.20.0
matplotlib >= 3.4.0
networkx >= 2.6.0
pandas >= 1.3.0
scipy >= 1.7.0
jupyter >= 1.0.0
```

### Mathematical Background
- Linear algebra (eigenvalues, SVD, orthonormal bases)
- Group theory (symmetric group S_N, Cayley graphs)
- Graph theory (directed graphs, topological sort)
- Information theory (Shannon entropy, Fisher information)
- Quantum mechanics basics (state vectors, Born rule)

## Quick Start

### Option 1: Logic Realism V2 (Recommended)
```bash
cd notebooks/Logic_Realism
jupyter notebook
# Start with 00, 01, 02 (Foundation Layer)
```

### Option 2: Historical Exploration
```bash
cd notebooks/approach_1
jupyter notebook
# Start with 00, 01, 02, then 03-05 (Worked Examples)
```

## Computational Requirements

| System Size | RAM | Runtime | Notebooks |
|-------------|-----|---------|-----------|
| N ≤ 4 | Any laptop | Minutes | All |
| N = 5 | ~1GB | ~10 min | Most |
| N = 6 | ~4GB | ~30 min | Foundational |
| N = 7-8 | ~8GB+ | Hours | Sampling only |

**Recommendation**: Start with N ≤ 4 for full analysis, N=5-6 for selected calculations

## Validation Status

### Logic Realism (V2)
- **Computational validation**: 100% (all notebooks execute successfully)
- **Mathematical consistency**: Verified (cross-notebook theorem dependencies)
- **Code correctness**: Confirmed (all assertions pass)
- **Total coverage**: 14/14 notebooks complete

### Approach 1 (Historical)
- **Validation status**: Complete V&V with I2PS integration
- **Framework completion**: 18/18 notebooks validated
- **Reproducibility**: All results deterministic (seeded RNG)

## Key Results (Computationally Validated)

| Property | Value | Source | Method |
|----------|-------|--------|--------|
| K(N) = N-2 | Exact for N≥3 | Notebook 02 | Triple proof (Mahonian, Coxeter, MaxEnt) |
| Born rule | P = \|a\|² | Notebook 03 | MaxEnt on constraint-filtered space |
| Fisher = Fubini-Study | Identity | Notebook 04 | Computational verification |
| Tsirelson bound | 2√2 | approach_1/13 | PSD constraint analysis |
| ρ₄ (feasibility) | 0.0938 | approach_1/01 | Exact counting + Monte Carlo |
| S₄ permutohedron | 24 vertices, 36 edges | approach_1/04 | Group theory + geometry |

## File Outputs

Notebooks generate results in `./outputs/` (created automatically):
- `*.png` - Geometric visualizations (permutohedra, graphs, spectra)
- `*.csv` - Numerical results (embedding metrics, distortions)
- `*.json` - Summary statistics (validation results, parameters)

## Common Issues & Solutions

| Issue | Solution |
|-------|----------|
| Memory error (N>6) | Limit to N≤6 for full enumeration |
| Missing outputs directory | Auto-created, or `os.makedirs('./outputs', exist_ok=True)` |
| Slow linear extensions | Use `limit=1000` parameter |
| NetworkX version | Use v2.6+ for `all_topological_sorts()` |

## Citation

If you use this code in research, please cite:

```bibtex
@misc{longmire2025plf,
  author = {Longmire, James D.},
  title = {Physical Logic Framework: Logic Realism and Logic Field Theory},
  year = {2025},
  url = {https://github.com/jdlongmire/physical-logic-framework},
  note = {Computational notebooks for quantum mechanics derivation from logical consistency}
}
```

## License

**Code**: Apache License 2.0
**Documentation**: CC-BY 4.0

## Support

**Author**: James D. (JD) Longmire
**Email**: longmire.jd@gmail.com
**ORCID**: 0009-0009-1383-7698

---

**Current Status** (October 9, 2025): Logic Realism V2 series complete (14 notebooks, ~37,000 words). All computational validation successful. Sprints 1-4 delivered. Lean formalization in progress (Sprint 6). Ready for paper integration and experimental proposal writing.
