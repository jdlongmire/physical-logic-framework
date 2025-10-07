# Lean 4 Proof Consultation - N=3 Constraint Enumeration

## Context
Working on Logic Field Theory formal proofs in Lean 4 with Mathlib. Need to complete two theorems with `sorry` placeholders.

## Query 1: Combinatorial Cardinality Proof

**Theorem**: `inversion_count_finite`
```lean
theorem inversion_count_finite {N : Nat} (σ : Equiv.Perm (Fin N)) :
  inversionCount σ ≤ N * (N - 1) / 2 := by
  unfold inversionCount
  have h_card_pairs : (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)).card = N * (N - 1) / 2 := by
    sorry -- Need: cardinality of ordered pairs {(i,j) : i < j} in Fin N
  have h_subset : (Finset.univ.filter (fun p => p.1 < p.2 ∧ σ p.1 > σ p.2)) ⊆
    (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)) := by
    intro x hx; simp at hx ⊢; exact hx.1
  exact Nat.le_trans (Finset.card_le_card h_subset) (h_card_pairs.le)
```

**Question**: What Mathlib theorem proves that |{(i,j) ∈ Fin N × Fin N : i < j}| = N*(N-1)/2?

Options considered:
- `Fintype.card_compl_eq_card_sub` (doesn't exist in current Mathlib)
- `Nat.choose_two_right` (seems related to C(N,2))
- `Finset.card_univ_diff`

**Request**: Provide the exact Mathlib theorem name and usage pattern for Lean 4.

---

## Query 2: Finite Group Enumeration

**Theorem**: `s3_complete`
```lean
lemma s3_complete (σ : Equiv.Perm (Fin 3)) :
  σ = id_3 ∨ σ = trans_01 ∨ σ = trans_02 ∨ σ = trans_12 ∨ σ = cycle_012 ∨ σ = cycle_021 := by
  sorry -- Need: exhaustive enumeration of S_3
```

Where:
- `id_3 = 1` (identity)
- `trans_01 = Equiv.swap 0 1`
- `trans_02 = Equiv.swap 0 2`
- `trans_12 = Equiv.swap 1 2`
- `cycle_012 = Equiv.swap 0 1 * Equiv.swap 1 2`
- `cycle_021 = Equiv.swap 0 2 * Equiv.swap 0 1`

**Question**: What's the best approach to prove exhaustive enumeration of Equiv.Perm (Fin 3)?

Options considered:
1. Use `Fintype.card_perm` to show |S_3| = 6, then `decide` on equality
2. Case analysis: `fin_cases σ 0 <;> fin_cases σ 1 <;> fin_cases σ 2` with injectivity elimination
3. Use Mathlib's existing S_n enumeration theorems

**Request**: Provide concrete proof strategy or Mathlib theorem that handles this pattern.

---

## Additional Context

**Environment**:
- Lean 4 (v4.23.0-rc2)
- Mathlib (latest compatible version)
- Target: Remove all `sorry` from N=3 proofs in FeasibilityRatio.lean

**Goal**: Complete formal verification that ValidArrangements(3) = 3 with full proofs (no axioms).

**Constraints**:
- Must work with current Mathlib API
- Prefer decidable computation where possible
- Keep proofs maintainable (not overly complex)

Please provide specific Lean 4 code examples if possible.
