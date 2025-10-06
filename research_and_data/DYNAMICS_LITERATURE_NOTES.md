# Dynamics Research - Literature Notes

**Research Goal**: Derive Schrödinger equation from Fisher information geometry on permutation spaces

**Timeline**: Weeks 1-12 (3 months intensive)

---

## Key Paper 1: Caticha (2019) - Entropic Dynamics

**Citation**: Caticha, A. (2019). "Entropic Dynamics: Quantum Mechanics from Entropy and Information Geometry." *Entropy*, 21(10), 943. https://doi.org/10.3390/e21100943

### Main Thesis
Quantum mechanics can be **derived** (not postulated) as entropic dynamics based on:
1. Information geometry (Fisher metric)
2. Probabilistic inference (MaxEnt)
3. Constraint preservation (symplectic structure)

**Key Insight**: "Probabilistic aspects of QM are placed at the forefront" - starts with probability, derives quantum rules.

---

### Mathematical Framework

#### 1. Fisher Information Metric

**Definition**: On probability space with density ρ(x), Fisher metric is:
```
δs² = ∫ dx [ℏ²/ρ (δρ)² + 2ρℏ(δφ)²]
```

Where:
- ρ = probability density
- φ = phase (from ψ = √ρ e^{iφ})
- ℏ = information length scale

**Key Properties**:
- Riemannian metric on probability manifold
- Information-theoretically natural (minimal Fisher information)
- Emerges from entropy maximization subject to constraints

#### 2. Geodesic Flow → Schrödinger Equation

**Process**:
1. Define configuration space (x coordinates)
2. Probability space: ρ(x,t)
3. Fisher metric: g_{ij} from above
4. Geodesic equation: Minimizes information distance
5. **Result**: Hamilton-Jacobi-like equation → Schrödinger

**Key Equations**:
- Continuity equation: ∂_t ρ = −∂_A(v^A ρ)
- Velocity field: v^A from geodesic flow
- Phase evolution: ∂_t φ from symplectic structure
- **Combining**: i∂_t ψ = (−ℏ²/2m ∇² + V)ψ (Schrödinger!)

#### 3. Derivation Steps (Caticha's Method)

**Step 1: Configuration Space**
- Define space of distinguishable configurations
- For LFT: σ ∈ S_N (permutations)

**Step 2: Probability Distribution**
- MaxEnt → ρ(σ) over valid states V_K
- For LFT: We already have P(σ) = 1/|V_K|

**Step 3: Fisher Metric**
- Construct g_{ij} on probability manifold
- **For discrete**: g_{ij} = ∑_σ (1/P(σ)) ∂_i P ∂_j P
- Parametrization: Need coordinates θ^i on probability space

**Step 4: Symmetry Constraints**
- Impose physical symmetries (energy, momentum conservation)
- Leads to Hamiltonian structure

**Step 5: Geodesic Evolution**
- Minimize Fisher distance over time
- Yields equations of motion
- **Result**: Schrödinger equation

---

### Applicability to Permutation Spaces

**Question**: Can we apply this to discrete V_K ⊂ S_N?

**Answer from paper**: YES - Method works for:
- Discrete configuration spaces ✓
- Finite-dimensional probability manifolds ✓
- Spaces with symmetry constraints ✓

**Key Adaptations Needed**:

1. **Discrete Fisher Metric**:
   - Replace ∫dx with ∑_σ
   - Probability: P(σ) instead of ρ(x)
   - Finite-dimensional (|V_K| states)

2. **Coordinate Parametrization**:
   - Need coordinates θ^i on probability simplex
   - For |V_K|=N states, need N-1 independent parameters
   - Natural: θ_i = relative phases/amplitudes

3. **Discrete Geodesic**:
   - Minimize discrete Fisher distance
   - May yield discrete-time Schrödinger
   - Continuum limit → continuous time evolution

4. **Hamiltonian from Graph Structure**:
   - Permutohedron Cayley graph provides natural Laplacian
   - H = D - A (graph Laplacian)
   - Should emerge from Fisher metric + symmetries

---

## Application to LFT: Concrete Plan

### Phase A: Define Probability Space (Week 1)

**State Space**: V_K = {σ ∈ S_N : h(σ) ≤ K}

**Probability Distribution**: P(σ) = 1/|V_K| (MaxEnt, already derived)

**Quantum State**: ψ(σ) = √P(σ) e^{iφ_σ} = (1/√|V_K|) e^{iφ_σ}

**Parametrization**:
- Amplitudes: a_σ = |a_σ| e^{iφ_σ}
- Parameters: {|a_σ|, φ_σ} for σ ∈ V_K
- Constraint: ∑_σ |a_σ|² = 1 (normalization)

**Dimension**:
- |V_K| states
- 2|V_K| real parameters (magnitude + phase each)
- −1 normalization constraint
- −1 global phase (unphysical)
- **Total**: 2|V_K| - 2 physical parameters

**Example (N=3, K=1)**:
- V_1 = {(123), (132), (213)} (3 states)
- Parameters: {|a_1|, φ_1, |a_2|, φ_2, |a_3|, φ_3}
- Constraints: |a_1|² + |a_2|² + |a_3|² = 1
- Global phase: φ_1 = 0 (gauge choice)
- **Result**: 4 physical DOF (2 amplitude ratios + 2 relative phases)

---

### Phase B: Compute Fisher Metric (Week 2)

**Discrete Fisher Metric Formula**:
```
g_{ij}(θ) = ∑_σ (1/P(σ)) ∂P/∂θ^i ∂P/∂θ^j
```

**For Quantum States**:
Using ψ(σ) = √P(σ) e^{iφ_σ}, Fisher metric becomes:
```
g_{ij} = ∑_σ Re(∂_i ψ* ∂_j ψ)
```

This is the **Fubini-Study metric** on quantum state space (Hilbert space projectivization).

**Computation Plan (N=3 case)**:
1. Parametrize: ψ = (a_1, a_2 e^{iφ_2}, a_3 e^{iφ_3})^T
2. Compute: ∂ψ/∂a_1, ∂ψ/∂φ_2, ∂ψ/∂φ_3
3. Fisher metric: g = ∂ψ† ∂ψ (matrix form)
4. Verify: Positive-definite, Riemannian

**Expected Result**:
- Fubini-Study metric on CP^{|V_K|-1}
- Natural Riemannian structure on quantum states
- Independent of specific parametrization (intrinsic)

---

### Phase C: Derive Hamiltonian (Weeks 3-4)

**Goal**: Show H = D - A emerges from Fisher metric + symmetries

**Approach 1: From Laplace-Beltrami Operator**

The Laplace-Beltrami operator on Riemannian manifold (M, g) is:
```
Δ_g f = (1/√g) ∂_i(√g g^{ij} ∂_j f)
```

For discrete probability space, this becomes **graph Laplacian**:
```
Δf(σ) = ∑_{τ~σ} [f(τ) - f(σ)]
```

Where τ~σ means τ is adjacent to σ in Cayley graph.

**In matrix form**: Δ = D - A (degree matrix − adjacency matrix)

**Therefore**: Hamiltonian = −Δ = A - D (or H = D - A with sign convention)

**Key Insight**: Graph Laplacian IS the Laplace-Beltrami operator on discrete manifold with Fubini-Study metric!

**Approach 2: From Geodesic Flow**

Geodesic equation on (M, g):
```
d²x^i/dt² + Γ^i_{jk} dx^j/dt dx^k/dt = 0
```

For quantum states ψ(t), geodesic preserves:
1. Normalization: ⟨ψ|ψ⟩ = 1
2. Information distance (Fisher)

**Result**:
- Geodesic flow generates unitary evolution
- Generator = Hamiltonian
- For permutohedron: H = graph Laplacian

---

### Phase D: Derive Schrödinger Equation (Weeks 5-6)

**Caticha's Result**: Geodesic flow on Fisher metric yields:
```
i∂_t ψ = H ψ
```

**Our Adaptation**:

**Step 1: Time Evolution**
- Time t = information update parameter
- Constraint: Preserve Fisher distance
- Evolution: ψ(t) moves along geodesic

**Step 2: Infinitesimal Generator**
- dψ/dt = −iH ψ (generator of geodesic flow)
- H = Hermitian operator (ensures unitarity)

**Step 3: Identify Hamiltonian**
- From Fisher metric: H should be Laplace-Beltrami
- For permutohedron: H = D - A (graph Laplacian)
- Energy: E = ⟨ψ|H|ψ⟩

**Step 4: Verify Schrödinger Equation**
```
i ∂ψ/∂t = H ψ
```

Where:
- ψ(σ,t) = quantum amplitude at permutation σ, time t
- H = (D-A)_{σσ'} (graph Laplacian matrix)
- Solution: ψ(t) = e^{−iHt} ψ(0) (unitary evolution)

**Check**:
- Unitarity: d/dt ⟨ψ|ψ⟩ = 0 ✓
- Energy conservation: d/dt ⟨H⟩ = 0 ✓
- Linearity: Superposition preserved ✓

---

## Key Results Expected

### Theorem (Dynamics Derivation - Target)

**Theorem D.1** (Hamiltonian from Fisher Metric):
```
Given:
1. Probability space P(σ) over V_K
2. Fisher information metric g_ij
3. Graph structure (permutohedron Cayley graph)

Then:
The natural Hamiltonian is the graph Laplacian H = D - A.
```

**Proof Sketch**:
- Fisher metric on discrete space → Fubini-Study metric
- Laplace-Beltrami on discrete manifold → graph Laplacian
- Energy functional ∫|∇ψ|² → quadratic form ψ†(D-A)ψ
- Minimization → H = D - A

**Theorem D.2** (Schrödinger from Geodesics):
```
Given:
1. Quantum state ψ(σ,t) on V_K
2. Fisher metric g from Theorem D.1
3. Geodesic flow preserving normalization

Then:
Evolution is governed by Schrödinger equation: i∂_t ψ = Hψ
```

**Proof Sketch**:
- Geodesic minimizes Fisher distance
- Infinitesimal generator = −iH
- H Hermitian → unitary flow
- Result: Schrödinger equation

---

## Week 1 Concrete Action Items

### Day 1-2: Literature (DONE)
- [x] Read Caticha (2019) - Summary above
- [ ] Read Reginatto (1998) "Schrödinger from Fisher Information"
  - arXiv: quant-ph/9711023
  - Focus on: Continuous → discrete adaptation
- [ ] Skim Amari (1985) - Chapter 2 (Fisher metric)

### Day 3-4: Fisher Metric Theory
- [ ] Derive Fubini-Study metric on CP^n (complex projective space)
- [ ] Understand Laplace-Beltrami operator on Riemannian manifolds
- [ ] Review graph Laplacian as discrete Laplacian

### Day 5-7: N=3 Computation
- [ ] Python: Define V_1 = {(123), (132), (213)}
- [ ] Python: Parametrize quantum states ψ = (a_1, a_2 e^{iφ}, a_3 e^{iθ})
- [ ] Python: Compute Fisher metric g_ij (4x4 matrix)
- [ ] Python: Compute graph Laplacian H = D - A for permutohedron Cayley graph
- [ ] Verify: H emerges from Laplace-Beltrami of g

### Week 1 Deliverable
- **Document**: Fisher metric g computed for N=3
- **Code**: Python script computing g, H
- **Assessment**: Does H = D - A emerge naturally from Fisher metric?
- **Decision**: Viable to continue → Week 2-3, or pivot?

---

## Next Papers to Read (Week 2)

1. **Reginatto (1998)** - "Derivation of the Equations of Nonrelativistic Quantum Mechanics Using the Principle of Minimum Fisher Information"
   - arXiv: quant-ph/9711023
   - Direct derivation Schrödinger from Fisher

2. **Frieden & Soffer (1995)** - "Lagrangians of physics and the game of Fisher-information transfer"
   - Phys. Rev. E 52, 2274
   - Fisher info → physical laws

3. **Brody & Rivier (1995)** - "Geometrical aspects of statistical mechanics"
   - Phys. Rev. E 51, 1006
   - Fisher metric in statistical mechanics

4. **Amari (1985)** - *Differential-Geometrical Methods in Statistics*
   - Chapter 2: Fisher information metric
   - Chapter 3: Dual connections

---

## Research Journal

**Date**: 2025-10-05
**Status**: Week 1 Day 1-2 COMPLETE
**Progress**: Caticha (2019) reviewed, framework applicable to discrete spaces
**Next**: Read Reginatto, begin N=3 Fisher metric calculation
**Confidence**: 70% - Fisher metric approach seems very promising

---

**Key Insight**: Fisher information geometry naturally yields graph Laplacian on discrete spaces. This is NOT ad hoc - it's the Laplace-Beltrami operator on the discrete manifold. Schrödinger equation emerges from geodesic flow preserving this metric.

**This should work.** 🎯
