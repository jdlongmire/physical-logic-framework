#!/usr/bin/env python3
"""Compute giant-component fraction vs K for permutations up to N_max.
Optimized by indexing permutations and using neighbor checks via adjacent transpositions.
Saves CSV and per-N plots under ./plots/.
"""
import argparse
from itertools import permutations, combinations
from collections import deque, defaultdict
import math
import csv
import os
import random

def inversion_count(t):
    c = 0
    n = len(t)
    for i in range(n):
        ai = t[i]
        for j in range(i+1,n):
            if ai > t[j]:
                c += 1
    return c

def build_perms(n):
    perms = [tuple(p) for p in permutations(range(n))]
    invs = [inversion_count(p) for p in perms]
    index = {p:i for i,p in enumerate(perms)}
    return perms, invs, index

def neighbors_tuple(p):
    n = len(p)
    for i in range(n-1):
        lst = list(p)
        lst[i], lst[i+1] = lst[i+1], lst[i]
        yield tuple(lst)

def component_sizes(indices_set, perms, index):
    # indices_set: set of indices allowed
    visited = set()
    sizes = []
    for i in indices_set:
        if i in visited:
            continue
        q = deque([i])
        visited.add(i)
        s = 0
        while q:
            u = q.popleft()
            s += 1
            for nbr in neighbors_tuple(perms[u]):
                v = index[nbr]
                if v in indices_set and v not in visited:
                    visited.add(v)
                    q.append(v)
        sizes.append(s)
    return sorted(sizes, reverse=True)

def run_sweep(n, out_rows, plot_dir, sample_threshold=2000, sample_k=500):
    perms, invs, index = build_perms(n)
    max_inv = max(invs)
    # For each K from 0..max_inv, compute |V_K| and giant component fraction
    for K in range(max_inv+1):
        indices = {i for i,inv in enumerate(invs) if inv <= K}
        size_vk = len(indices)
        if size_vk == 0:
            out_rows.append((n, K, 0, 0, 0.0))
            continue
        if size_vk <= sample_threshold:
            sizes = component_sizes(indices, perms, index)
            largest = sizes[0]
        else:
            # sample: BFS from random seeds (up to sample_k) to estimate largest component
            seeds = random.sample(list(indices), min(10, len(indices)))
            best = 0
            for s in seeds:
                q = deque([s])
                seen = {s}
                while q and len(seen) < sample_k:
                    u = q.popleft()
                    for nbr in neighbors_tuple(perms[u]):
                        v = index[nbr]
                        if v in indices and v not in seen:
                            seen.add(v)
                            q.append(v)
                best = max(best, len(seen))
            largest = best
        frac = largest / size_vk if size_vk>0 else 0.0
        out_rows.append((n, K, size_vk, largest, round(frac,6)))

def write_csv(path, rows):
    with open(path, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['N','K','|V_K|','largest_component_size','largest_fraction'])
        for r in rows:
            w.writerow(r)

def ensure_dir(d):
    os.makedirs(d, exist_ok=True)

def try_plot(n, rows, plot_dir):
    try:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
    except Exception:
        return
    ks = [r[1] for r in rows if r[0]==n]
    fracs = [r[4] for r in rows if r[0]==n]
    plt.figure(figsize=(6,3))
    plt.plot(ks, fracs, marker='o')
    plt.xlabel('K')
    plt.ylabel('Largest component fraction')
    plt.title(f'N={n} giant-component curve')
    plt.grid(True)
    plt.tight_layout()
    plt.savefig(os.path.join(plot_dir, f'giant_component_N_{n}.png'))
    plt.close()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--min-n', type=int, default=3)
    parser.add_argument('--max-n', type=int, default=8)
    parser.add_argument('--out', type=str, default='ChatGPT_K_N_R&D/giant_component_curve.csv')
    parser.add_argument('--plot-dir', type=str, default='ChatGPT_K_N_R&D/plots')
    args = parser.parse_args()
    ensure_dir(args.plot_dir)
    rows = []
    for n in range(args.min_n, args.max_n+1):
        print(f'Running N={n}')
        run_sweep(n, rows, args.plot_dir)
        try_plot(n, rows, args.plot_dir)
    write_csv(args.out, rows)
    print('Done, wrote', args.out)

if __name__ == '__main__':
    main()
