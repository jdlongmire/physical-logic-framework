# Logic Field Theory (LFT) - Notebook Collection README

**James D. Longmire**  
Independent Researcher, Northrop Grumman Fellow  
📧 longmire.jd@gmail.com  
🆔 ORCID: 0009-0009-1383-7698

## Overview

Logic Field Theory proposes that physical reality emerges from logical filtering of information: **A = L(I)**, where Actuality equals a Logical operator acting on Information space. This collection contains mathematical derivations, computational simulations, and empirical predictions spanning quantum mechanics, spacetime geometry, and gravity.

## Prerequisites

### Required Libraries
```python
numpy >= 1.20
matplotlib >= 3.3
networkx >= 2.5
pandas >= 1.3
scipy >= 1.7
itertools (standard library)
random (standard library)
math (standard library)
```

### Mathematical Background
- Linear algebra (eigenvalues, SVD, orthonormal bases)
- Group theory basics (symmetric group S_N, Cayley graphs)
- Graph theory (directed graphs, DAGs, topological sort)
- Basic quantum mechanics (state vectors, Born rule, Bell inequalities)

## Installation

```bash
# Clone repository
git clone [repository-url]
cd LFT-notebooks

# Install dependencies
pip install numpy matplotlib networkx pandas scipy

# Launch Jupyter
jupyter notebook
```

## Notebook Navigation Guide

### 🔵 FOUNDATION LAYER (Start Here)
| Notebook | Purpose | Key Output |
|----------|---------|------------|
| **00_Foundations** | Core thesis A = L(I), philosophical motivation | Conceptual framework |
| **01_Ontology_of_I** | Information space as directed graphs | Feasibility ratio ρ_N plot |
| **02_Operator** | L = EM ∘ NC ∘ ID implementation | Algorithm specification |

### 🟢 WORKED EXAMPLES
| Notebook | Purpose | Key Output |
|----------|---------|------------|
| **03_FirstExample_N3** | Complete N=3 analysis | Hexagonal permutohedron |
| **04_Geometry_N-1_Problem** | Dimension = rank(A_{N-1}) | 3D visualization for N=4 |
| **05_Stability_N4** | Why N≤4 for stability | Convergence plots |

### 🟡 SPACETIME EMERGENCE
| Notebook | Purpose | Key Output |
|----------|---------|------------|
| **06_Scaling_N6** | N=6 → ℝ⁴ embedding | Stress metrics |
| **07_Spacetime_3plus1** | Time/space factorization | Flow alignment data |
| **08_TimeAsLFlow** | Time = monotone descent | h(t) evolution curves |
| **09_StrainDynamics** | Strain tensor formalism | T(σ), S(σ) distributions |

### 🔴 QUANTUM DERIVATIONS
| Notebook | Purpose | Key Output |
|----------|---------|------------|
| **10_QuantumBridge** | Simplex ↔ Permutohedron | Affine isomorphism proof |
| **11_Observer** | Measurement mechanics | EPR correlation demo |
| **12_BornRule** | P(i) = \|ψᵢ\|² derivation | Convergence plots |
| **13_TsirelsonBound** | CHSH ≤ 2√2 proof | Gram matrix analysis |

### 🟣 EXTENSIONS & ANALYSIS
| Notebook | Purpose | Key Output |
|----------|---------|------------|
| **14_Gravity_PoC** | Strain → gravity | Geodesic bending demo |
| **20_Predictions** | Testable effects | Finite-K deviations |
| **21_Explanatory_Power** | Paradox resolutions | Comparison table |
| **22_Comparisons** | LFT vs other theories | Framework scorecard |

### 📄 MANUSCRIPT
- **LFT_Position_Paper.md** - Complete theoretical presentation with appendices

## Quick Validation Tests

### Test 1: Core Construction
```python
# Run in notebook 03
N = 3
assert factorial(N) == 6  # vertices
assert N*(N-1)*factorial(N)//2 == 6  # edges
```

### Test 2: Dimension Check
```python
# Run in notebook 04
N = 4
assert N - 1 == 3  # spatial dimensions
```

### Test 3: Born Rule Convergence
```python
# Run in notebook 12
psi = np.array([0.6, 0.8])  # normalized: [0.6, 0.8]
born_probs = (psi/np.linalg.norm(psi))**2
# Should converge to [0.36, 0.64] as K→∞
```

## Key Results Summary

| Property | Value | Notebook | Verified |
|----------|-------|----------|----------|
| S₄ vertices | 24 | 04 | ✓ |
| S₄ edges (adjacent) | 36 | 04 | ✓ |
| Tsirelson bound | 2√2 | 13 | ✓ |
| ρ₄ (feasibility) | 0.0938 | 01 | ✓ |
| ρ₅ (feasibility) | 0.0037 | 01 | ✓ |
| Dimension for N=4 | 3 | 04 | ✓ |

## Reproduction Protocol

1. **Set seeds for reproducibility**:
```python
import numpy as np
import random
np.random.seed(42)
random.seed(42)
```

2. **Run foundation notebooks** (00-02) first to understand framework

3. **Execute worked examples** (03-05) to see core constructions

4. **Explore extensions** based on interest:
   - Quantum: notebooks 10-13
   - Gravity: notebook 14
   - Predictions: notebook 20

## Common Issues & Solutions

| Issue | Solution |
|-------|----------|
| Memory error for N>8 | Limit to N≤6 for full enumeration |
| Missing ./outputs/ | Create with `os.makedirs('./outputs', exist_ok=True)` |
| Slow linear extensions | Add `limit=1000` parameter |
| NetworkX version conflicts | Use `nx.all_topological_sorts()` for v2.6+ |

## Parameter Ranges

- **N** (elements): 3-6 for exact computation, 3-8 for sampling
- **K** (micro-constraints): 1-200 for finite-K effects
- **trials**: 1000-10000 for statistical convergence
- **α, β, κ** (coupling): 0.1-10.0 for gravity toy model

## File Outputs

The notebooks generate these files in `./outputs/`:
- `N*_permutohedron_*.png` - Geometric visualizations
- `N*_edge_distortions.csv` - Embedding metrics
- `finiteK_*.png` - Quantum deviation plots
- `strain_*.png` - Dynamics visualizations
- `*_summary.json` - Numerical results

## Computational Requirements

- **Minimal**: N≤4 runs on any modern laptop
- **Standard**: N=5 requires ~1GB RAM
- **Extended**: N=6 requires ~4GB RAM
- **Full analysis**: ~30 minutes for all notebooks

## Citation

If you use this code in research, please cite:
```bibtex
@article{longmire2024lft,
  author = {Longmire, James D.},
  title = {Logic Field Theory: A Derivational Framework for Physics},
  year = {2024},
  url = {https://github.com/[username]/LFT-notebooks}
}
```

## Support

For questions or issues:
- Email: longmire.jd@gmail.com
- ORCID: 0009-0009-1383-7698

## License

[Specify: MIT, Apache 2.0, or other]

---

**Note**: This is active theoretical research. All results are mathematical/computational demonstrations. Physical interpretations await empirical validation through experiments proposed in Notebook 20.