#!/usr/bin/env python3
"""Enumerate inversion counts (Mahonian numbers) and test K(N) candidates.

Writes CSV with columns: N, K_candidate, N_valid, total_permutations, match_candidate
"""
import argparse
import csv
import math
from itertools import permutations


def inversion_count(perm):
    # perm: tuple of integers 0..N-1
    inv = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                inv += 1
    return inv


def mahonian_counts(n):
    # returns list M[k] = number of permutations of size n with k inversions
    max_inv = n*(n-1)//2
    M = [0] * (max_inv+1)
    for p in permutations(range(n)):
        k = inversion_count(p)
        M[k] += 1
    return M


def cumulative_counts(M, K):
    return sum(M[:K+1])


def run(max_n, out_path):
    rows = []
    for n in range(1, max_n+1):
        M = mahonian_counts(n)
        total = math.factorial(n)
        # candidate: K = n-2 (use max(0, n-2))
        Kcand = max(0, n-2)
        N_valid_cand = cumulative_counts(M, Kcand)
        rows.append((n, Kcand, N_valid_cand, total))
    # write CSV
    with open(out_path, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['N', 'K_candidate', 'N_valid_candidate', 'total_permutations', 'fraction_valid'])
        for r in rows:
            n, K, nv, total = r
            writer.writerow([n, K, nv, total, nv/total])
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=8)
    parser.add_argument('--out', dest='out', default='results_N_1_10.csv')
    args = parser.parse_args()
    rows = run(args.max_n, args.out)
    for r in rows:
        n, K, nv, total = r
        print(f'N={n:2d} K={K:2d} N_valid={nv:6d} total={total:6d} frac={nv/total:.6f}')
