#!/usr/bin/env python3
"""
Enumerate S₄ with inversion counts to guide Lean implementation

Generates systematic naming and inversion count verification for all 24 permutations.
"""

from itertools import permutations
from collections import defaultdict

def inversion_count(perm):
    """Count inversions: pairs (i,j) where i < j but perm[i] > perm[j]"""
    count = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                count += 1
    return count

def perm_to_cycle_type(perm):
    """Determine cycle type of a permutation"""
    n = len(perm)
    visited = [False] * n
    cycles = []

    for i in range(n):
        if visited[i]:
            continue

        cycle = []
        j = i
        while not visited[j]:
            visited[j] = True
            cycle.append(j)
            j = perm[j]

        if len(cycle) > 1:
            cycles.append(len(cycle))

    cycles.sort(reverse=True)
    return tuple(cycles) if cycles else (1,)

def perm_to_name(perm):
    """Generate a descriptive name for the permutation"""
    if perm == (0, 1, 2, 3):
        return "id"

    cycle_type = perm_to_cycle_type(perm)

    # Classify by cycle type
    if cycle_type == (2,):
        # Single transposition
        diffs = [(i, perm[i]) for i in range(4) if perm[i] != i]
        if len(diffs) == 2:
            i, j = diffs[0][0], diffs[0][1]
            return f"swap_{i}{j}"

    elif cycle_type == (2, 2):
        # Double transposition
        diffs = [(i, perm[i]) for i in range(4) if perm[i] != i]
        pairs = set()
        for i, j in diffs:
            pairs.add(tuple(sorted([i, j])))
        pairs_str = "_".join([f"{a}{b}" for a, b in sorted(pairs)])
        return f"double_{pairs_str}"

    elif cycle_type == (3,):
        # 3-cycle
        # Find the cycle
        for start in range(4):
            if perm[start] != start:
                cycle = [start]
                current = perm[start]
                while current != start:
                    cycle.append(current)
                    current = perm[current]
                if len(cycle) == 3:
                    return f"cycle3_{''.join(map(str, cycle))}"

    elif cycle_type == (4,):
        # 4-cycle
        cycle = [0]
        current = perm[0]
        while current != 0:
            cycle.append(current)
            current = perm[current]
        return f"cycle4_{''.join(map(str, cycle))}"

    # Fallback
    return f"perm_{''.join(map(str, perm))}"

def main():
    """Enumerate all S₄ permutations with inversion counts"""

    print("=" * 80)
    print("S_4 Enumeration with Inversion Counts")
    print("=" * 80)
    print()

    # Collect all permutations
    all_perms = list(permutations(range(4)))

    # Group by inversion count
    by_inversions = defaultdict(list)
    for perm in all_perms:
        h = inversion_count(perm)
        name = perm_to_name(perm)
        by_inversions[h].append((perm, name))

    # Print summary
    print(f"Total permutations: {len(all_perms)}")
    print()

    # Print by inversion count
    for h in sorted(by_inversions.keys()):
        perms = by_inversions[h]
        print(f"Inversion count h = {h}: {len(perms)} permutations")
        for perm, name in sorted(perms):
            perm_str = "".join(map(str, perm))
            cycle_type = perm_to_cycle_type(perm)
            print(f"  {perm_str} | {name:25s} | cycle_type={cycle_type}")
        print()

    # Count valid arrangements (h ≤ 3)
    valid = []
    for h in range(4):
        if h in by_inversions:
            valid.extend(by_inversions[h])

    print("=" * 80)
    print(f"VALID ARRANGEMENTS (h <= 3): {len(valid)} permutations")
    print("=" * 80)
    print()

    for perm, name in sorted(valid, key=lambda x: (inversion_count(x[0]), x[0])):
        h = inversion_count(perm)
        perm_str = "".join(map(str, perm))
        print(f"  h={h} | {perm_str} | {name}")

    print()
    print("=" * 80)
    print("LEAN 4 DEFINITIONS (suggested)")
    print("=" * 80)
    print()

    for h in sorted(by_inversions.keys()):
        if h > 3:
            continue
        perms = by_inversions[h]
        print(f"-- Inversion count h = {h}")
        for perm, name in sorted(perms):
            # Generate Lean definition
            if name == "id":
                print(f"def s4_{name} : Equiv.Perm (Fin 4) := 1")
            elif name.startswith("swap_"):
                i, j = name.split("_")[1]
                print(f"def s4_{name} : Equiv.Perm (Fin 4) := Equiv.swap {i} {j}")
            elif name.startswith("cycle3_"):
                cycle = name.split("_")[1]
                if len(cycle) == 3:
                    a, b, c = cycle
                    # (a b c) = (a b) * (b c)
                    print(f"def s4_{name} : Equiv.Perm (Fin 4) := Equiv.swap {a} {b} * Equiv.swap {b} {c}")
            elif name.startswith("cycle4_"):
                cycle = name.split("_")[1]
                if len(cycle) == 4:
                    a, b, c, d = cycle
                    # (a b c d) = (a b) * (b c) * (c d)
                    print(f"def s4_{name} : Equiv.Perm (Fin 4) := Equiv.swap {a} {b} * Equiv.swap {b} {c} * Equiv.swap {c} {d}")
            elif name.startswith("double_"):
                # Double transposition
                pairs = name.split("_")[1]
                if len(pairs) == 4:
                    i, j, k, l = pairs
                    print(f"def s4_{name} : Equiv.Perm (Fin 4) := Equiv.swap {i} {j} * Equiv.swap {k} {l}")
            else:
                print(f"-- TODO: def s4_{name} : Equiv.Perm (Fin 4) := ???")
        print()

if __name__ == "__main__":
    main()
