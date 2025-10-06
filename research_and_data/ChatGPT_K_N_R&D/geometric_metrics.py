#!/usr/bin/env python3
"""Geometric metrics on V_K subgraphs of the permutohedron.
For each N and K, compute:
 - number of nodes |V_K|
 - number of connected components
 - size of largest component
 - fraction of nodes in largest component
 - diameter of largest component (BFS)
 - average shortest path length within largest component (approx)

Writes CSV with these metrics for N in range and K in [0..max_inv].
"""
from itertools import permutations
import csv
import argparse
from collections import deque
import math


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


def build_VK(n, K):
    all_perms = list(permutations(range(n)))
    M = {p: inversion_count(p) for p in all_perms}
    V = [p for p in all_perms if M[p] <= K]
    Vset = set(V)
    return V, Vset


def connected_components(V, Vset):
    unvisited = set(V)
    comps = []
    while unvisited:
        start = next(iter(unvisited))
        q = deque([start])
        comp = {start}
        unvisited.remove(start)
        while q:
            u = q.popleft()
            for v in neighbors_adjacent(u):
                if v in Vset and v not in comp:
                    comp.add(v)
                    unvisited.discard(v)
                    q.append(v)
        comps.append(comp)
    return comps


def bfs_distances(start, comp_set):
    # BFS return distances dict from start to nodes in comp_set
    q = deque([start])
    dist = {start: 0}
    while q:
        u = q.popleft()
        for v in neighbors_adjacent(u):
            if v in comp_set and v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
    return dist


def diameter_and_avgdist(comp):
    # comp: set of nodes; compute diameter and average shortest path length within comp
    nodes = list(comp)
    if len(nodes) <= 1:
        return 0, 0.0
    total_dist = 0
    max_d = 0
    pairs = 0
    # For small comps perform all-pairs BFS
    for u in nodes:
        d = bfs_distances(u, comp)
        # sum distances to nodes > u to avoid double counting
        for v in nodes:
            if v == u: continue
            if v in d:
                total_dist += d[v]
                max_d = max(max_d, d[v])
                pairs += 1
            else:
                # disconnected inside comp? shouldn't happen
                pass
    avg = total_dist / pairs if pairs > 0 else 0.0
    return max_d, avg


def analyze(N):
    max_inv = N * (N-1) // 2
    results = []
    for K in range(0, max_inv+1):
        V, Vset = build_VK(N, K)
        nv = len(V)
        if nv == 0:
            results.append((N, K, 0, 0, 0, 0.0, 0.0))
            continue
        comps = connected_components(V, Vset)
        num_comps = len(comps)
        largest = max(comps, key=lambda c: len(c))
        size_largest = len(largest)
        frac = size_largest / nv
        diam, avgd = diameter_and_avgdist(largest)
        results.append((N, K, nv, num_comps, size_largest, frac, diam, avgd))
    return results


def run(min_n, max_n, out_csv):
    rows = []
    for N in range(min_n, max_n+1):
        print(f'Analyzing N={N}...')
        r = analyze(N)
        rows.extend(r)
    with open(out_csv, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['N','K','|V|','num_components','size_largest','frac_largest','diameter_largest','avgdist_largest'])
        for row in rows:
            writer.writerow(row)
    return rows

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--min-n', type=int, default=3)
    parser.add_argument('--max-n', type=int, default=9)
    parser.add_argument('--out', default='geometric_metrics_results_N_3_9.csv')
    args = parser.parse_args()
    run(args.min_n, args.max_n, args.out)
