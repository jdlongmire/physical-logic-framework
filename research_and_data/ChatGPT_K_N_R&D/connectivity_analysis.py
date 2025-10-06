#!/usr/bin/env python3
"""Connectivity analysis for V_K: permutations with inversion count <= K
Compute minimal K such that V_K (as subgraph of permutohedron with adjacent-transposition edges)
is connected. Writes results to stdout and CSV.
"""
from itertools import permutations
import csv
import argparse
from collections import deque


def inversion_count(perm):
    inv = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                inv += 1
    return inv


def neighbors_adjacent(perm):
    # yield permutations reachable by swapping adjacent elements
    n = len(perm)
    for i in range(n-1):
        lst = list(perm)
        lst[i], lst[i+1] = lst[i+1], lst[i]
        yield tuple(lst)


def build_VK(n, K):
    all_perms = list(permutations(range(n)))
    M = {p: inversion_count(p) for p in all_perms}
    V = [p for p in all_perms if M[p] <= K]
    Vset = set(V)
    return V, Vset


def is_connected(V, Vset):
    if not V:
        return False
    start = V[0]
    visited = set([start])
    q = deque([start])
    while q:
        u = q.popleft()
        for v in neighbors_adjacent(u):
            if v in Vset and v not in visited:
                visited.add(v)
                q.append(v)
    return len(visited) == len(V)


def find_minimal_connected_K(n):
    max_inv = n*(n-1)//2
    for K in range(0, max_inv+1):
        V, Vset = build_VK(n, K)
        if is_connected(V, Vset):
            return K, len(V)
    return None, 0


def run(max_n, out_csv):
    rows = []
    for n in range(1, max_n+1):
        Kmin, size = find_minimal_connected_K(n)
        rows.append((n, Kmin, size))
        print(f'N={n:2d}: K_min_connected={Kmin}, |V|={size}')
    with open(out_csv, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['N','K_min_connected','size_V'])
        for r in rows:
            writer.writerow(r)
    return rows

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=10)
    parser.add_argument('--out', default='connectivity_results_N_1_10.csv')
    args = parser.parse_args()
    run(args.max_n, args.out)
