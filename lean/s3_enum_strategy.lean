/-
Strategy for proving s3_complete enumeration
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm

-- Define our 6 permutations
def id_3 : Equiv.Perm (Fin 3) := 1
def trans_01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def trans_02 : Equiv.Perm (Fin 3) := Equiv.swap 0 2
def trans_12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
def cycle_012 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
def cycle_021 : Equiv.Perm (Fin 3) := Equiv.swap 0 2 * Equiv.swap 0 1

-- STRATEGY 1: Use decidability on finite permutations
-- Since Equiv.Perm (Fin 3) is a Fintype with DecidableEq,
-- we can use `decide` if we enumerate explicitly

-- STRATEGY 2: Functional extensionality approach
-- Case on σ 0, σ 1, σ 2 and use injectivity to eliminate impossible cases

lemma s3_complete_v1 (σ : Equiv.Perm (Fin 3)) :
  σ = id_3 ∨ σ = trans_01 ∨ σ = trans_02 ∨ σ = trans_12 ∨ σ = cycle_012 ∨ σ = cycle_021 := by
  -- Extract where σ sends each element
  have h0 := σ 0
  have h1 := σ 1
  have h2 := σ 2
  -- Use Fin.fin_cases or similar to enumerate all possibilities
  -- Then use injectivity/surjectivity to eliminate invalid combinations
  sorry

-- STRATEGY 3: Use Fintype.card and show our list is complete
-- First prove there are exactly 6 distinct permutations in our list
-- Then prove |S_3| = 6
-- Then show equality by decidability

#check Fintype.card_perm -- Shows |Perm (Fin n)| = n!

lemma s3_has_six : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Fintype.card_perm]
  rfl

-- Our list of 6
def s3_list : List (Equiv.Perm (Fin 3)) :=
  [id_3, trans_01, trans_02, trans_12, cycle_012, cycle_021]

-- STRATEGY 4: Direct decidable equality check using Finset.univ
-- Since we know Finset.univ has all 6 permutations,
-- we can check membership decidably

lemma s3_complete_v2 (σ : Equiv.Perm (Fin 3)) :
  σ = id_3 ∨ σ = trans_01 ∨ σ = trans_02 ∨ σ = trans_12 ∨ σ = cycle_012 ∨ σ = cycle_021 := by
  -- Use that σ ∈ Finset.univ and Finset.univ.card = 6
  -- Then show our 6 are distinct and in Finset.univ
  -- So they must be all elements
  sorry
