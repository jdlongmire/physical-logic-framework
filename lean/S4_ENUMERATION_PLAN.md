# S₄ Enumeration Plan - Phase 3

**Goal**: Prove ValidArrangements(4) = 9

**Constraint**: K(4) = 3, so we need all σ ∈ S₄ with h(σ) ≤ 3

---

## S₄ Structure (24 permutations)

### By Cycle Type

1. **Identity** (1 permutation)
   - (e): h(σ) = 0

2. **Transpositions** (6 permutations)
   - Swap 2 adjacent elements
   - (01), (02), (03), (12), (13), (23)
   - h(σ) = 1 each

3. **3-Cycles** (8 permutations)
   - Rotate 3 elements
   - (012), (013), (023), (123), (021), (031), (032), (132)
   - h(σ) varies: 2-3

4. **4-Cycles** (6 permutations)
   - Rotate all 4 elements
   - (0123), (0132), (0213), (0231), (0312), (0321)
   - h(σ) varies: 3-6

5. **Double Transpositions** (3 permutations)
   - Two disjoint swaps
   - (01)(23), (02)(13), (03)(12)
   - h(σ) = 2 each

---

## Expected Result

**From computational notebooks**: ValidArrangements(4) = 9

**Predicted valid permutations (h ≤ 3)**:
- Identity: 1 permutation (h=0)
- Transpositions: 6 permutations (h=1 each)
- Some 3-cycles: ~2 permutations (h=2)
- **Total**: ~9 permutations

---

## Implementation Strategy

### Step 1: Systematic Naming Convention

Use cycle notation in definitions:
```lean
def s4_id : Equiv.Perm (Fin 4) := 1
def s4_swap_01 : Equiv.Perm (Fin 4) := Equiv.swap 0 1
def s4_cycle_012 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
```

### Step 2: Organize by Expected Inversion Count

**Priority 1** (definitely valid, h ≤ 1):
- Identity
- 6 transpositions

**Priority 2** (likely valid, h = 2-3):
- Double transpositions
- Short 3-cycles

**Priority 3** (check carefully):
- Longer 3-cycles
- 4-cycles

### Step 3: Computational Verification

Before defining in Lean, verify in Python:
```python
from itertools import permutations

def inversion_count(perm):
    count = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                count += 1
    return count

# Enumerate all S_4
for p in permutations(range(4)):
    h = inversion_count(p)
    if h <= 3:
        print(f"{p}: h={h}")
```

### Step 4: Lean Implementation

1. Define all 24 permutations
2. Prove inversion counts using `decide`
3. Filter by constraint h ≤ 3
4. Prove the set equals the 9 valid ones

---

## Inversion Count Reference

**Formula**: h(σ) = |{(i,j) : i < j and σ(i) > σ(j)}|

**Maximum**: For Fin 4, max inversions = 4*3/2 = 6
- This occurs for reversed permutation (3,2,1,0)

---

## Challenges

1. **Volume**: 24 permutations vs 6 for S₃
2. **Complexity**: Some 3-cycles and 4-cycles have subtle inversion counts
3. **Enumeration**: Need s4_complete lemma (like s3_complete)
4. **Verification**: All inversion counts must be computationally verified

---

## Success Criteria

✅ All 24 permutations defined in Lean
✅ Inversion count proven for each
✅ Filter by h ≤ 3 identifies exactly 9 permutations
✅ n_four_constraint_derivation proven
✅ Build succeeds with no errors in N=4 section

---

## Estimated Effort

- **Define 24 permutations**: 1-2 hours
- **Compute inversions**: 1-2 hours
- **Prove constraint enumeration**: 2-4 hours
- **Debug and verify**: 2-4 hours
- **Total**: 6-12 hours of focused work

---

## Next Immediate Step

Create Python script to enumerate all S₄ with inversion counts, then systematically transfer to Lean.
