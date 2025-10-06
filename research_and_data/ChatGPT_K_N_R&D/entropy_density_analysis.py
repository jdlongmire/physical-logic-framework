#!/usr/bin/env python3
"""Compute entropy density log|V_K|/(N-1) for N range and find K that maximizes it.
Writes CSV with columns: N, K_peak, |V_K_peak|, K_candidate(N-2), |V_K_candidate|, note
"""
from itertools import permutations
import math
import csv
import argparse


def inversion_count(perm):
    inv = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                inv += 1
    return inv


def mahonian_counts(n):
    max_inv = n*(n-1)//2
    M = [0] * (max_inv+1)
    for p in permutations(range(n)):
        k = inversion_count(p)
        M[k] += 1
    return M


def cumulative_counts(M):
    cum = []
    s = 0
    for m in M:
        s += m
        cum.append(s)
    return cum


def run(min_n, max_n, out_csv):
    rows = []
    for n in range(min_n, max_n+1):
        M = mahonian_counts(n)
        cum = cumulative_counts(M)
        best_K = None
        best_val = -1.0
        best_size = None
        for K, size in enumerate(cum):
            if size == 0:
                continue
            ed = math.log(size) / max(1, (n-1))
            if ed > best_val:
                best_val = ed
                best_K = K
                best_size = size
        Kcand = max(0, n-2)
        size_cand = cum[Kcand]
        rows.append((n, best_K, best_size, Kcand, size_cand, best_K == Kcand))
        print(f'N={n:2d}: K_peak={best_K}, |V|={best_size}, Kcand={Kcand}, |Vcand|={size_cand}, match={best_K==Kcand}')
    with open(out_csv, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['N','K_peak','size_peak','K_candidate','size_candidate','match'])
        for r in rows:
            writer.writerow(r)
    return rows

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--min-n', type=int, default=3)
    parser.add_argument('--max-n', type=int, default=10)
    parser.add_argument('--out', default='entropy_density_results_N_3_10.csv')
    args = parser.parse_args()
    run(args.min_n, args.max_n, args.out)
