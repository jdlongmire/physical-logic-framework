# K(N) = (N-1) - 1: Deep Investigation

**Goal**: Understand WHY K = (N-1) - 1 is exact, given that codimension ≠ 1

**Key Constraint**: The formula K = dim(permutohedron) - 1 is EXACT for all N, but our simple "codimension-1 flow" explanation fails computationally.

**Status**: ACTIVE INVESTIGATION

---

## What We Know For Certain

### 1. The Formula is Exact
- N=3: K=1, dim=2, K = 2-1 ✓
- N=4: K=2, dim=3, K = 3-1 ✓
- N=5: K=3, dim=4, K = 4-1 ✓
- N=6: K=4, dim=5, K = 5-1 ✓

**This holds perfectly. It's not approximate.**

### 2. But V_K Spans Full Dimension
From computational test:
- dim(V_{N-2}) = N-1 (the FULL permutohedron dimension)
- Codimension = 0, not 1

**So V_K doesn't define a lower-dimensional submanifold.**

### 3. Yet Symmetry Split Works
- Bijection proof: |{h≤N-2}| = |{h≥complement}| ✓
- MaxEnt: Symmetry preservation ✓
- Empirical: 8/8 validation ✓

**The formula works, we just don't fully understand why geometrically.**

---

## Hypotheses to Test

### Hypothesis 1: Generator Count Relationship

**Observation**: S_N has exactly N-1 adjacent transposition generators
- τ₁ = (12), τ₂ = (23), ..., τ_{N-1} = (N-1,N)

**Formula**: K = N-2 = (number of generators) - 1

**Test**: Does K=N-2 have special relationship to generators?

**From earlier test**:
- N=3: 2 generators, all contained in V_1 (K=1=N-2) ✓
- N=4: 3 generators, all contained in V_1 (K=1<N-2=2) ✗
- N=5: 4 generators, all contained in V_1 (K=1<N-2=3) ✗

**Conclusion**: K=N-2 is NOT minimal for containing all generators (K=1 is).

**But**: Maybe it's about INDEPENDENT generators?

**New angle**: Coxeter presentation of A_{N-1}

The Coxeter group A_{N-1} ≅ S_N has:
- **Rank**: N-1 (number of simple reflections)
- **Generators**: s₁, s₂, ..., s_{N-1} (adjacent transpositions)
- **Relations**:
  - s_i² = 1 (involutions)
  - (s_is_{i+1})³ = 1 (braid relations for adjacent generators)
  - (s_is_j)² = 1 for |i-j| ≥ 2 (commuting relations)

**Question**: Does K=N-2 relate to the number of relations?

Count of relations:
- Involution relations: N-1
- Braid relations: N-2 (for i=1 to N-2)
- Commuting relations: (N-1 choose 2) - (N-2) = ...

Wait, the braid relations are N-2! That's K!

**Potential connection**: K = N-2 = number of braid relations in Coxeter presentation!

---

### Hypothesis 2: Braid Relation Connection

**Coxeter group A_{N-1}** has presentation:
```
Generators: s₁, s₂, ..., s_{N-1}
Relations:
  1. s_i² = 1 for all i                    [N-1 relations]
  2. (s_is_{i+1})³ = 1 for i=1,...,N-2    [N-2 relations] ← THIS IS K!
  3. (s_is_j)² = 1 for |i-j| ≥ 2           [other relations]
```

**The braid relations**: (s_is_{i+1})³ = 1

There are exactly **N-2** of these (for i = 1, 2, ..., N-2).

**Hypothesis**: K=N-2 counts the braid relations, which are the "essential" relations for non-commutativity.

**Interpretation**:
- Involution relations (N-1): Tell us generators are self-inverse
- Commuting relations: Tell us distant generators commute
- **Braid relations (N-2)**: Encode the non-abelian structure!

**Connection to h ≤ K**:
- Each braid relation involves TWO adjacent generators
- Violating a braid relation = allowing more than 3 alternating applications
- K=N-2 might limit violations of these essential relations

**Test**: Does h(σ) count braid relation violations?

Actually, h(σ) counts inversions, not braid violations directly. But maybe there's a connection?

---

### Hypothesis 3: Degrees of Freedom in Group Action

**Setup**: S_N acts on itself by left multiplication.

**Orbit-stabilizer**: For any σ ∈ S_N, the orbit has size N!/|Stab(σ)|.

**Degrees of freedom**: In a group with N-1 generators, a "generic" element requires specifying N-1 coordinates.

**But**: To constrain the system while preserving dynamics, need to "free" one generator.

**Formula**: Constrained generators = (N-1) - 1 = N-2 = K

**Interpretation**:
- N-1 generators available
- Fix N-2 of them (constraint)
- Leave 1 free (dynamics)
- This gives K = N-2

**Analogy**: Like fixing N-2 coordinates in (N-1)-dimensional space, leaving 1 coordinate free for motion.

**But why this specific way of constraining?**

The constraint h(σ) ≤ K limits the "complexity" of the permutation. Maybe:
- h(σ) measures how many generators needed to reach σ from identity
- K=N-2 limits this to N-2 generators
- Leaves 1 generator "free"

**Test**: Does h(σ) ≤ N-2 mean σ can be written using at most N-2 generators?

Actually, no. The minimal length of σ (in Cayley graph) can be different from h(σ).

---

### Hypothesis 4: Information-Theoretic Constraint

**Shannon entropy**: H[P] = log₂|V_K|

For K=N-2:
- N=3: H ≈ 1.58 bits
- N=4: H ≈ 3.17 bits
- N=5: H ≈ 4.86 bits
- N=6: H ≈ 6.61 bits

**Compare to log₂(N!)**:
- N=3: log₂(6) ≈ 2.58 bits (ratio: 1.58/2.58 = 0.61)
- N=4: log₂(24) ≈ 4.58 bits (ratio: 3.17/4.58 = 0.69)
- N=5: log₂(120) ≈ 6.91 bits (ratio: 4.86/6.91 = 0.70)
- N=6: log₂(720) ≈ 9.49 bits (ratio: 6.61/9.49 = 0.70)

**Observation**: Ratio stabilizes around 0.70 for large N.

**But** how does this relate to (N-1) - 1?

**Alternative**: Maybe it's about the entropy per dimension?

H/dim = H/(N-1):
- N=3: 1.58/2 = 0.79 bits/dim
- N=4: 3.17/3 = 1.06 bits/dim
- N=5: 4.86/4 = 1.22 bits/dim
- N=6: 6.61/5 = 1.32 bits/dim

This is growing, approaching some asymptotic value?

Not obviously connected to K=N-2...

---

### Hypothesis 5: Constraint Function Structure

**The function h: S_N → ℕ** has special properties:

1. **h(e) = 0** (identity has no inversions)
2. **h(σ_max) = N(N-1)/2** (reversal has maximum inversions)
3. **h is a homomorphism**? No, h is not additive.
4. **h defines a partial order**? Not quite, but related.

**Key property**: h counts violations of natural order.

**Natural order**: 1 < 2 < 3 < ... < N

**Inversion**: Pair (i,j) where i<j but σ(i)>σ(j) violates this.

**Maximum violations possible**: (N choose 2) = N(N-1)/2

**Question**: How many violations can we tolerate while preserving "essential" order structure?

**If we allow K=N-2 violations**:
- Out of N(N-1)/2 possible inversions
- We allow up to N-2
- Ratio: (N-2)/(N(N-1)/2) = 2(N-2)/(N(N-1)) → 0 as N → ∞

**Interpretation**: For large N, K=N-2 allows a vanishingly small fraction of possible inversions.

**But why N-2 specifically? Why not N-3 or N-1?**

---

## New Computational Test: Braid Relation Hypothesis

Let me test if K=N-2 braid relations have a special role:

```python
def count_braid_violations(perm):
    """
    Count how many braid relations (s_i s_{i+1})^3 = 1 are violated
    """
    N = len(perm)
    violations = 0

    for i in range(N-2):
        # Check if applying s_i then s_{i+1} three times returns to perm
        # This is complex to compute directly...

        # Simpler: Check if local pattern violates braid
        # The braid relation says s_i and s_{i+1} don't commute normally
        # but (s_i s_{i+1})^3 = identity

        # Actually, let me think about what this means...
        pass

    return violations
```

Actually, this is getting complicated. The braid relations are about the GROUP structure, not about individual permutations.

Let me think differently...

---

## Alternative Approach: Word Length

**Definition**: The word length ℓ(σ) is the minimal number of adjacent transpositions needed to express σ.

**Relation to inversions**: ℓ(σ) = h(σ) (these are equal for S_N!)

**So**: h(σ) ≤ K means σ can be expressed as a product of at most K adjacent transpositions.

**For K=N-2**: σ is expressible using at most N-2 adjacent transpositions.

**But there are N-1 generators total.**

**Question**: What permutations require ALL N-1 generators?

**Answer**: The longest element in S_N requires ℓ(σ_max) = N(N-1)/2 transpositions.

**But**: Many permutations can be reached using fewer than N-1 DISTINCT generators.

**Hypothesis**: K=N-2 limits us to permutations reachable using at most N-2 of the N-1 generators?

**Test**: For each σ ∈ V_{N-2}, determine how many distinct generators are needed.

---

## Most Promising Direction: Braid Relations

After reviewing, the strongest connection is:

**Number of braid relations in A_{N-1} = N-2 = K**

This can't be coincidence. The braid relations are the "essential" non-abelian structure of S_N.

**Proposed interpretation**:
- The N-1 generators can be partially ordered: s₁, s₂, ..., s_{N-1}
- Adjacent pairs (s_i, s_{i+1}) have braid relations: N-2 such pairs
- Non-adjacent pairs commute
- **K=N-2 constrains the "braid complexity"** somehow

**Connection to h(σ) ≤ K**:
- Permutations with h(σ) ≤ N-2 have limited "braiding"
- They don't fully explore the non-abelian structure
- This preserves some abelian-like properties?

**Next step**: Formalize this connection.

---

## Action Plan

### Immediate (Next 2 hours):

1. **Literature search**: "Coxeter groups", "braid relations", "word length A_{N-1}"
   - Find if K=rank-1 appears in standard Coxeter theory

2. **Test generator usage**: For each σ ∈ V_{N-2}, count distinct generators needed
   - Does K=N-2 limit to using at most N-2 distinct generators?

3. **Check Coxeter number**: The Coxeter number h of A_{N-1} is N
   - We have K=N-2, rank=N-1, h_Coxeter=N
   - Relation: K = h_Coxeter - 2 = rank - 1
   - Is this significant?

### Follow-up (Days 2-3):

4. **Formal group theory analysis**: Consult expert or textbook on A_{N-1} structure

5. **Prove braid connection**: If braid relation count = K is key, formalize the argument

6. **Integrate into paper**: Once understood, add to Section 4.5

---

## Current Best Guess

**Hypothesis (to be proven)**:

> K = N-2 equals the number of braid relations in the Coxeter group A_{N-1}. This is not coincidence: the constraint h(σ) ≤ K limits permutations to those with "bounded braid complexity," preserving enough structure for logical dynamics while allowing MaxEnt symmetry.

**Evidence**:
- Exact match: K = N-2 = (# braid relations) ✓
- Braid relations encode essential non-commutativity ✓
- This explains why (N-1) - 1 without needing codimension-1 ✓

**Next**: Prove this rigorously.

