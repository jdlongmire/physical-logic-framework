#!/usr/bin/env python3
"""Compute normalized-Laplacian spectral gap (second-smallest eigenvalue) for V_K largest component
for each K=0..max_inv for N in given range. Saves CSV.
"""
import argparse
from itertools import permutations
from collections import deque
import csv
import os
import math

def inversion_count(t):
    c = 0
    n = len(t)
    for i in range(n):
        ai = t[i]
        for j in range(i+1,n):
            if ai > t[j]:
                c += 1
    return c

def neighbors_tuple(p):
    n = len(p)
    for i in range(n-1):
        lst = list(p)
        lst[i], lst[i+1] = lst[i+1], lst[i]
        yield tuple(lst)

def build_perms(n):
    perms = [tuple(p) for p in permutations(range(n))]
    invs = [inversion_count(p) for p in perms]
    index = {p:i for i,p in enumerate(perms)}
    return perms, invs, index

def largest_component_indices(indices, perms, index):
    visited = set()
    best_comp = []
    for i in indices:
        if i in visited:
            continue
        q = deque([i])
        visited.add(i)
        comp = [i]
        while q:
            u = q.popleft()
            for nbr in neighbors_tuple(perms[u]):
                v = index[nbr]
                if v in indices and v not in visited:
                    visited.add(v)
                    q.append(v)
                    comp.append(v)
        if len(comp) > len(best_comp):
            best_comp = comp
    return best_comp

def spectral_gap_component(component_indices, perms, index):
    n = len(component_indices)
    if n <= 1:
        return 0.0
    idx_map = {v:i for i,v in enumerate(component_indices)}
    adj = [[] for _ in range(n)]
    for v in component_indices:
        i = idx_map[v]
        for nbr in neighbors_tuple(perms[v]):
            w = index[nbr]
            if w in idx_map:
                adj[i].append(idx_map[w])
    # build sparse adjacency
    try:
        import numpy as np
        from scipy.sparse import csr_matrix, diags
        from scipy.sparse.linalg import eigsh
    except Exception:
        # fallback to dense numpy
        import numpy as np
        adj_mat = np.zeros((n,n))
        for i, nbrs in enumerate(adj):
            for j in nbrs:
                adj_mat[i,j] = 1.0
        deg = adj_mat.sum(axis=1)
        D_inv_sqrt = np.diag([1.0/math.sqrt(d) if d>0 else 0.0 for d in deg])
        L = np.eye(n) - D_inv_sqrt.dot(adj_mat).dot(D_inv_sqrt)
        from numpy.linalg import eigh
        vals = eigh(L)[0]
        vals = sorted(vals)
        return float(vals[1]) if len(vals)>1 else float(vals[0])
    # sparse path
    rows = []
    cols = []
    data = []
    deg = [len(a) for a in adj]
    for i, nbrs in enumerate(adj):
        for j in nbrs:
            rows.append(i); cols.append(j); data.append(1.0)
    A = csr_matrix((data, (rows, cols)), shape=(n,n))
    D_inv_sqrt = diags([1.0/math.sqrt(d) if d>0 else 0.0 for d in deg])
    L = csr_matrix((np.identity(n))) - D_inv_sqrt.dot(A).dot(D_inv_sqrt)
    try:
        vals, vecs = eigsh(L, k=2, which='SM')
        vals = sorted(vals)
        return float(vals[1])
    except Exception:
        Ld = L.toarray()
        from numpy.linalg import eigh
        vals = eigh(Ld)[0]
        vals = sorted(vals)
        return float(vals[1]) if len(vals)>1 else float(vals[0])

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--min-n', type=int, default=3)
    parser.add_argument('--max-n', type=int, default=8)
    parser.add_argument('--out', type=str, default='ChatGPT_K_N_R&D/spectral_sweep.csv')
    args = parser.parse_args()
    rows = []
    for n in range(args.min_n, args.max_n+1):
        print('N=', n)
        perms, invs, index = build_perms(n)
        max_inv = max(invs)
        for K in range(max_inv+1):
            indices = {i for i,inv in enumerate(invs) if inv <= K}
            size_vk = len(indices)
            if size_vk == 0:
                rows.append((n,K,0,0,0.0))
                continue
            comp = largest_component_indices(indices, perms, index)
            largest = len(comp)
            gap = spectral_gap_component(comp, perms, index)
            rows.append((n,K,size_vk,largest,gap))
    with open(args.out, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['N','K','|V_K|','largest_component_size','spectral_gap'])
        for r in rows:
            w.writerow(r)
    print('Wrote', args.out)

if __name__ == '__main__':
    main()
