#!/usr/bin/env python3
"""Faster geometric metrics focused around candidate K = N-2.
- Precomputes permutations and inversion counts once per N.
- Scans K in window [0 .. min(N-2 + window, max_inv)] by default window=2.
- Computes connected components; for large components, estimates diameter and avg-distance by sampling.
- Safer for N up to 9-10.

Outputs CSV with: N,K,|V|,num_components,size_largest,frac_largest,diameter_est,avgdist_est,notes
"""
from itertools import permutations
import csv
import argparse
from collections import deque
import math
import random

random.seed(0)


def inversion_count(perm):
    inv = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                inv += 1
    return inv


def neighbors_adjacent(perm):
    n = len(perm)
    for i in range(n-1):
        lst = list(perm)
        lst[i], lst[i+1] = lst[i+1], lst[i]
        yield tuple(lst)


def build_all_perms_and_inversions(n):
    all_perms = list(permutations(range(n)))
    invs = [inversion_count(p) for p in all_perms]
    return all_perms, invs


def build_V_indices(all_perms, invs, K):
    # return list of indices of permutations with inversion <= K and a set for fast membership
    V_idx = [i for i, v in enumerate(invs) if v <= K]
    V_set = set(V_idx)
    return V_idx, V_set


def connected_components_indices(all_perms, V_idx, V_set):
    # Work with indices to reduce tuple hashing overhead
    unvisited = set(V_idx)
    comps = []
    while unvisited:
        start = next(iter(unvisited))
        q = deque([start])
        comp = {start}
        unvisited.remove(start)
        while q:
            u = q.popleft()
            perm_u = all_perms[u]
            for vperm in neighbors_adjacent(perm_u):
                try:
                    v = all_perms.index(vperm)
                except ValueError:
                    # linear search fallback; but all_perms.index is expensive
                    # To avoid this, we will create a mapping outside this function in the caller
                    continue
                if v in V_set and v not in comp:
                    comp.add(v)
                    unvisited.discard(v)
                    q.append(v)
        comps.append(comp)
    return comps


def build_neighbors_index_map(all_perms):
    # mapping permutation tuple -> index for O(1) neighbor lookup
    return {p: i for i, p in enumerate(all_perms)}


def connected_components_indices_fast(all_perms, V_idx, V_set, perm_to_idx):
    unvisited = set(V_idx)
    comps = []
    while unvisited:
        start = next(iter(unvisited))
        q = deque([start])
        comp = {start}
        unvisited.remove(start)
        while q:
            u = q.popleft()
            perm_u = all_perms[u]
            for vperm in neighbors_adjacent(perm_u):
                v = perm_to_idx.get(vperm)
                if v is None:
                    continue
                if v in V_set and v not in comp:
                    comp.add(v)
                    unvisited.discard(v)
                    q.append(v)
        comps.append(comp)
    return comps


def bfs_distances_index(start_idx, all_perms, comp_set, perm_to_idx, max_nodes=None):
    q = deque([start_idx])
    dist = {start_idx: 0}
    while q:
        u = q.popleft()
        perm_u = all_perms[u]
        for vperm in neighbors_adjacent(perm_u):
            v = perm_to_idx.get(vperm)
            if v is None: continue
            if v in comp_set and v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
                if max_nodes and len(dist) > max_nodes:
                    return dist
    return dist


def estimate_diameter_avgdist(all_perms, comp, perm_to_idx, sample_size=10, max_bfs_nodes=5000):
    nodes = list(comp)
    if len(nodes) <= 1:
        return 0, 0.0
    sample_nodes = nodes if len(nodes) <= sample_size else random.sample(nodes, sample_size)
    max_d = 0
    total_d = 0
    count = 0
    for u in sample_nodes:
        d = bfs_distances_index(u, all_perms, comp, perm_to_idx, max_nodes=max_bfs_nodes)
        # accumulate distances from u to reachable nodes in component
        for v, dist in d.items():
            if v == u: continue
            total_d += dist
            count += 1
            if dist > max_d: max_d = dist
    avg = (total_d / count) if count > 0 else 0.0
    return max_d, avg


def analyze(N, window=2, sample_size=12, max_bfs_nodes=5000):
    all_perms, invs = build_all_perms_and_inversions(N)
    perm_to_idx = build_neighbors_index_map(all_perms)
    max_inv = N * (N-1) // 2
    Kcand = max(0, N-2)
    Kmax = min(max_inv, Kcand + window)
    results = []
    for K in range(0, Kmax + 1):
        V_idx, V_set = build_V_indices(all_perms, invs, K)
        nv = len(V_idx)
        if nv == 0:
            results.append((N, K, 0, 0, 0, 0.0, 0, 0.0, 'empty'))
            continue
        comps = connected_components_indices_fast(all_perms, V_idx, V_set, perm_to_idx)
        num_comps = len(comps)
        largest = max(comps, key=lambda c: len(c))
        size_largest = len(largest)
        frac = size_largest / nv
        # For large largest components, estimate metrics by sampling
        if size_largest <= 2000:
            diam, avgd = estimate_diameter_avgdist(all_perms, largest, perm_to_idx, sample_size=max( min(50, size_largest), 5), max_bfs_nodes=max_bfs_nodes)
            note = 'exact-sampled'
        else:
            diam, avgd = estimate_diameter_avgdist(all_perms, largest, perm_to_idx, sample_size=sample_size, max_bfs_nodes=max_bfs_nodes)
            note = 'approx-sampled'
        results.append((N, K, nv, num_comps, size_largest, frac, diam, avgd, note))
    return results


def run(min_n, max_n, out_csv, window=2):
    rows = []
    for N in range(min_n, max_n+1):
        print(f'Analyzing N={N}... (window around K=N-2)')
        r = analyze(N, window=window)
        rows.extend(r)
    with open(out_csv, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['N','K','|V|','num_components','size_largest','frac_largest','diameter_est','avgdist_est','note'])
        for row in rows:
            writer.writerow(row)
    return rows

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--min-n', type=int, default=3)
    parser.add_argument('--max-n', type=int, default=9)
    parser.add_argument('--out', default='geometric_metrics_fast_results_N_3_9.csv')
    parser.add_argument('--window', type=int, default=2, help='scan K up to N-2+window')
    args = parser.parse_args()
    run(args.min_n, args.max_n, args.out, window=args.window)
