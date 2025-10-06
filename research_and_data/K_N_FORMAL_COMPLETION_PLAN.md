# K(N) = N-2 Formal Completion Plan

**Goal**: Achieve rigorous mathematical proof of the symmetry split property and derive closed form if possible

**Status**: Symmetry split discovered computationally (6/6 verification), seeking formal proof

---

## Current State

### What We Know ✅

1. **Computational verification** (N=3-8):
   ```
   Σ_{i=0}^{N-2} M(N,i) = Σ_{i=c}^{max} M(N,i)
   ```
   where c = (N²-3N+4)/2, max = N(N-1)/2

2. **Sequence identified**: Our |V_{N-2}| values [3, 9, 29, 98, 343, 1230, 4489, 16599]

3. **OEIS connections**:
   - A008302: Mahonian numbers triangle M(n,k)
   - A161169: Cumulative Mahonian triangle T(n,k) = Σ_{i=0}^k M(n,i)
   - A001893: Permutations with n-3 inversions (similar but different sequence)

4. **Known formulas from A161169**:
   - Recurrence: T(n,k) = T(n,k-1) + T(n-1,k) - T(n-1,k-n)
   - Complement: T(n,k) = n! - T(n, n(n-1)/2-k-1)
   - Generating function: Product approach

### What We Need 🎯

1. **Formal proof**: Symmetry split theorem holds for all N
2. **Closed form**: Explicit formula for |V_{N-2}| = T(N, N-2)
3. **Necessity argument**: Why MaxEnt MUST select K=N-2

---

## Approach 1: Symmetry Split via Mahonian Reflection

### Strategy
Use the known symmetry M(n,k) = M(n, max-k) to prove cumulative symmetry.

### Theorem to Prove

**Symmetry Split Theorem**:

For all N ≥ 3, define:
- K = N - 2
- max = N(N-1)/2
- c = max - K = (N²-3N+4)/2

Then:
```
T(N, K) = T(N, max) - T(N, c-1)
```

where T(N,k) = Σ_{i=0}^k M(N,i).

Since T(N, max) = N! (all permutations), this becomes:
```
T(N, N-2) = N! - T(N, c-1)
```

### Proof Sketch

**Claim**: T(N, c-1) = T(N, N-2)

**Approach**:
1. Use reflection symmetry: M(N,i) = M(N, max-i)
2. Show that the interval [0, N-2] reflects to interval [c, max]
3. Verify: max - (N-2) = c
4. Therefore cumulative sums are equal

**Verification of reflection**:
```
max - K = N(N-1)/2 - (N-2)
        = (N² - N - 2N + 4)/2
        = (N² - 3N + 4)/2
        = c ✓
```

**Bijection argument**:
- Map each k ∈ [0, N-2] to max-k ∈ [c, max]
- By symmetry M(N,k) = M(N,max-k)
- Therefore sums are equal

### Implementation

```python
def prove_symmetry_split_formal(N):
    """
    Formal verification of symmetry split for specific N
    """
    K = N - 2
    max_inv = N * (N - 1) // 2
    c = max_inv - K

    # Compute Mahonian distribution
    mahonian = compute_mahonian_distribution(N)

    # Verify reflection symmetry
    for k in range(max_inv // 2 + 1):
        assert mahonian[k] == mahonian[max_inv - k], f"Symmetry broken at k={k}"

    # Verify cumulative sums
    sum_low = sum(mahonian[i] for i in range(K+1))
    sum_high = sum(mahonian[i] for i in range(c, max_inv+1))

    # Bijection check
    sum_via_reflection = sum(mahonian[max_inv - i] for i in range(K+1))

    assert sum_low == sum_high, "Symmetry split failed"
    assert sum_high == sum_via_reflection, "Bijection failed"

    return True, {
        'K': K,
        'complement': c,
        'sum_low': sum_low,
        'sum_high': sum_high,
        'verified': True
    }
```

**Status**: Can verify computationally for any N, provides constructive proof via bijection

---

## Approach 2: Closed Form via Recurrence Relation

### From A161169

**Recurrence**:
```
T(n,k) = T(n,k-1) + T(n-1,k) - T(n-1,k-n)
```

**For k = n-2**:
```
T(n, n-2) = T(n, n-3) + T(n-1, n-2) - T(n-1, 2-n)
```

Since k-n = n-2-n = -2 < 0, we have T(n-1, 2-n) = 0.

Therefore:
```
T(n, n-2) = T(n, n-3) + T(n-1, n-2)
```

**This gives us a recurrence!**

### Recurrence Implementation

```python
def V_K_recurrence(N, memo={}):
    """
    Compute |V_{N-2}| using recurrence relation
    """
    if N in memo:
        return memo[N]

    # Base cases
    if N == 3:
        return 3
    if N == 4:
        return 9

    # Recurrence: T(n,n-2) = T(n,n-3) + T(n-1,n-2)
    # Need to compute T(N, N-3) and T(N-1, N-3)

    # This requires computing partial sums...
    # Actually this recurrence is more complex than initially appears

    # Let me use the general recurrence properly
    # T(n,k) = T(n,k-1) + T(n-1,k) - T(n-1,k-n)

    # For our case: k = n-2
    # T(n,n-2) = T(n,n-3) + T(n-1,n-2) - T(n-1,-2)
    # Since T(n-1,-2) = 0, we get:
    # T(n,n-2) = T(n,n-3) + T(n-1,n-2)

    result = compute_T_n_k(N, N-3) + V_K_recurrence(N-1, memo)
    memo[N] = result
    return result
```

**Challenge**: This requires computing T(N, N-3) which is also a partial sum. We need the full Mahonian distribution.

### Alternative: Matrix Formulation

Can we express the recurrence as a matrix equation and find eigenvalues?

```
[T(n,n-2)]   [a b] [T(n-1,n-2)]
[T(n,n-3)] = [c d] [T(n-1,n-3)]
```

This might yield a closed form via characteristic polynomial.

---

## Approach 3: q-Factorial Generating Function

### Theory

The Mahonian generating function is:
```
Σ_k M(n,k) q^k = [n]_q!
```

where [n]_q! = (1-q)(1-q²)...(1-q^n) / (1-q)^n (q-factorial)

### Partial Sum

We want:
```
|V_{n-2}| = Σ_{k=0}^{n-2} M(n,k)
```

This is the coefficient sum in [n]_q! for powers q^0 through q^{n-2}.

**Equivalently**:
```
|V_{n-2}| = [n]_q! · (1-q^{n-1})/(1-q) |_{q→1-}
```

Actually, we want the sum of coefficients, so:
```
|V_{n-2}| = ∫_0^1 (partial [n]_q!) dq (?)
```

This approach is tricky because we're summing specific coefficients, not evaluating at a point.

### Coefficient Extraction

Use Cauchy residue theorem:
```
|V_{n-2}| = (1/2πi) ∮ [n]_q! · (1-q^{n-1})/(1-q) · dq/q
```

This gives an exact formula but requires complex analysis to evaluate.

---

## Approach 4: Combinatorial Bijection Proof

### Strategy

Prove symmetry split by constructing explicit bijection between:
- Low set: L = {σ : h(σ) ≤ n-2}
- High set: H = {σ : h(σ) ≥ (n²-3n+4)/2}

### Bijection Candidate

**Map**: φ(σ) = reversal of σ (σ^R)

**Property**: h(σ^R) = max - h(σ) = n(n-1)/2 - h(σ)

**Check**: Does σ ∈ L map to φ(σ) ∈ H?

If h(σ) ≤ n-2, then:
```
h(σ^R) = n(n-1)/2 - h(σ)
       ≥ n(n-1)/2 - (n-2)
       = (n²-3n+4)/2
       = c
```

So φ(σ) ∈ H ✓

**Inverse**: φ^{-1} = φ (reversal is self-inverse)

**Conclusion**: This gives an explicit bijection L ↔ H, proving |L| = |H|!

### Formalization

**Theorem** (Symmetry Split via Reversal Bijection):

Let S_n be the symmetric group, h: S_n → ℕ the inversion count, and:
- L_n = {σ ∈ S_n : h(σ) ≤ n-2}
- H_n = {σ ∈ S_n : h(σ) ≥ (n²-3n+4)/2}

Define reversal map φ: S_n → S_n by φ(σ)(i) = σ(n-i).

Then:
1. φ is an involution: φ ∘ φ = id
2. φ(L_n) = H_n (reversal maps low to high)
3. |L_n| = |H_n| (cardinalities equal)

**Proof**:
1. Straightforward: reversing twice gives original
2. For σ ∈ L_n, h(φ(σ)) = max - h(σ) ≥ max - (n-2) = c, so φ(σ) ∈ H_n
3. Since φ is bijective, |L_n| = |φ(L_n)| = |H_n|

**QED** ✓

---

## Approach 5: Asymptotic Formula

### From A001893

The OEIS entry A001893 (similar sequence) gives asymptotic:
```
a(n) ~ 2^(2n-4) / sqrt(π n) · Q
```
where Q ≈ 0.2888 (digital search tree constant).

### Can we derive our asymptotic?

Our exponential fit gave:
```
|V_{n-2}| / n! ≈ 2.4 · exp(-0.56n)
```

Therefore:
```
|V_{n-2}| ≈ 2.4 · n! · exp(-0.56n)
```

Using Stirling: n! ≈ sqrt(2πn) (n/e)^n

```
|V_{n-2}| ≈ 2.4 · sqrt(2πn) · (n/e)^n · e^{-0.56n}
          ≈ 2.4 · sqrt(2πn) · n^n · e^{-n-0.56n}
          ≈ 2.4 · sqrt(2πn) · n^n · e^{-1.56n}
          ≈ C · sqrt(n) · (n/e^{1.56})^n
```

This gives exponential growth ~ (n/4.76)^n with polynomial prefactor.

**Can prove this rigorously** using saddle-point method on generating function.

---

## Action Plan for Formal Completion

### Phase 1: Bijection Proof (PRIORITY - 1-2 days) ✅

**Goal**: Formalize the reversal bijection proof

**Tasks**:
1. Write formal theorem statement
2. Prove φ(L_n) = H_n rigorously
3. Verify complement formula c = (n²-3n+4)/2
4. Add to paper as Theorem 4.5.2

**Status**: **READY TO IMPLEMENT** - proof is constructive and complete

**Output**: Formal proof document for paper

### Phase 2: Recurrence Analysis (2-3 days)

**Goal**: Derive recurrence relation for |V_{n-2}|

**Tasks**:
1. Use A161169 recurrence T(n,k) = T(n,k-1) + T(n-1,k) - T(n-1,k-n)
2. Specialize to k = n-2
3. Solve recurrence if possible
4. Compare to computational values

**Challenge**: Recurrence couples T(n,n-2) to T(n,n-3), requiring nested computation

**Fallback**: Document recurrence even if closed form not found

### Phase 3: Generating Function (3-5 days, OPTIONAL)

**Goal**: Extract closed form from q-factorial

**Tasks**:
1. Express |V_{n-2}| as coefficient sum in [n]_q!
2. Use Cauchy residue theorem for extraction
3. Evaluate contour integral (complex analysis)

**Challenge**: Requires advanced complex analysis techniques

**Fallback**: State generating function formulation even if not fully solved

### Phase 4: Lean Formalization (1-2 weeks, STRETCH GOAL)

**Goal**: Mechanically verify proof in Lean 4

**Tasks**:
1. Formalize Mahonian numbers in Lean
2. Define reversal map and inversion count
3. Prove bijection theorem
4. Verify for N=3,4,5 computationally

**Status**: Depends on Mathlib's combinatorics library

---

## Deliverables

### For Paper (Required)

1. **Theorem 4.5.2** (Symmetry Split via Bijection):
   - Formal statement
   - Complete proof using reversal map
   - Geometric interpretation

2. **Corollary 4.5.3** (K(N) Necessity):
   - K=N-2 is unique threshold preserving symmetry
   - Connection to MaxEnt principle

3. **Remark** (Open Problems):
   - Closed form for |V_{N-2}| remains open
   - Asymptotic formula from generating function
   - Connection to A001893 sequence

### For Research (Optional)

4. **Lean formalization** of Theorem 4.5.2
5. **Recurrence solution** if found
6. **OEIS submission** if sequence is new
7. **Follow-up paper** on Mahonian partial sums

---

## Timeline

**Week 1** (Current):
- ✅ Symmetry split discovery
- ✅ Computational verification
- ✅ OEIS search
- [ ] Bijection proof formalization

**Week 2**:
- [ ] Paper integration (Theorem 4.5.2)
- [ ] Recurrence analysis
- [ ] Asymptotic derivation

**Week 3-4** (Stretch):
- [ ] Generating function approach
- [ ] Lean formalization
- [ ] OEIS submission if applicable

---

## Success Criteria

### Minimum (Paper Acceptance):
- ✅ Computational verification (N=3-8)
- ✅ Geometric interpretation (permutohedron balls)
- ✅ MaxEnt connection (symmetry preservation)
- [ ] **Formal bijection proof** ← THIS IS KEY

### Ideal (Mathematical Completeness):
- [ ] Closed form for |V_{N-2}|
- [ ] Recurrence relation solved
- [ ] Generating function evaluated
- [ ] Lean mechanical verification

### Excellent (Research Contribution):
- [ ] New OEIS sequence submitted
- [ ] Follow-up paper on Mahonian sums
- [ ] Connection to broader combinatorics literature

---

## Current Status Summary

**Achieved**:
- Symmetry split discovered ✅
- Computational proof (N=3-8) ✅
- Geometric interpretation ✅
- Paper section drafted ✅

**Next Critical Step**:
- **Formalize bijection proof** (1-2 days)
- This is SUFFICIENT for publication

**Long-term Goals**:
- Closed form (nice to have)
- Generating function (research contribution)
- Lean formalization (gold standard)

**Bottom Line**: We can achieve formal completion sufficient for publication within 1-2 days by completing the bijection proof. The remaining goals are valuable but not blocking.

