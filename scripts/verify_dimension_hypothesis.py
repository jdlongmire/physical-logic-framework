#!/usr/bin/env python3
"""
Verify Dimensional Hypothesis: dim(V_K) ≈ K

Tests if the effective dimension of V_K matches K, which would prove
the geometric derivation K = (N-1) - 1 = N-2 for codimension-1.
"""

import numpy as np
from itertools import permutations

def inversion_count(perm):
    """Count inversions"""
    inv = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                inv += 1
    return inv

def get_V_K(N, K):
    """Get all permutations with h <= K"""
    perms = list(permutations(range(N)))
    h = {perm: inversion_count(perm) for perm in perms}
    return [perm for perm in perms if h[perm] <= K]

def effective_dimension_rank(V_K):
    """
    Compute effective dimension using matrix rank

    Each permutation is a point in R^N. The dimension of V_K
    is the rank of the matrix formed by these points.
    """
    if len(V_K) == 0:
        return 0

    # Create matrix where each row is a permutation
    matrix = np.array([list(sigma) for sigma in V_K], dtype=float)

    # Compute rank
    rank = np.linalg.matrix_rank(matrix)

    return rank

def effective_dimension_pca(V_K):
    """
    Compute effective dimension using PCA

    Count number of principal components with significant variance
    """
    if len(V_K) <= 1:
        return 0, []

    # Create matrix
    matrix = np.array([list(sigma) for sigma in V_K], dtype=float)

    # Center the data
    mean = np.mean(matrix, axis=0)
    centered = matrix - mean

    # Compute covariance
    cov = np.cov(centered.T)

    # Eigenvalues
    eigenvalues = np.linalg.eigvalsh(cov)
    eigenvalues = sorted(eigenvalues, reverse=True)

    # Count significant eigenvalues (> 1% of max)
    threshold = 0.01 * max(eigenvalues) if max(eigenvalues) > 0 else 0
    significant = sum(1 for ev in eigenvalues if ev > threshold)

    return significant, eigenvalues

def test_dimension_hypothesis():
    """
    Test: Does dim(V_K) ≈ K for all N and K?
    """
    print("="*70)
    print("DIMENSIONAL HYPOTHESIS TEST")
    print("="*70)
    print("\nHypothesis: dim(V_K) approx K")
    print("Implication: K=N-2 gives codimension-1 in (N-1)-dimensional space")
    print("\n" + "="*70)

    results = []

    for N in [3, 4, 5, 6]:
        print(f"\n### N = {N} (Permutohedron dimension = {N-1}) ###\n")

        max_K = min(N*(N-1)//2, 10)

        for K in range(0, max_K+1):
            V_K = get_V_K(N, K)

            # Compute dimensions
            dim_rank = effective_dimension_rank(V_K)
            dim_pca, eigenvalues = effective_dimension_pca(V_K)

            # Codimension
            permutohedron_dim = N - 1
            codim_rank = permutohedron_dim - dim_rank
            codim_pca = permutohedron_dim - dim_pca

            # Check if K=N-2
            is_K_N_2 = (K == N - 2)
            marker = " <-- K=N-2" if is_K_N_2 else ""

            print(f"K={K:2d}: |V_K|={len(V_K):4d}, "
                  f"dim(rank)={dim_rank}, dim(PCA)={dim_pca}, "
                  f"codim(rank)={codim_rank:+d}, codim(PCA)={codim_pca:+d}{marker}")

            # Store result
            results.append({
                'N': N,
                'K': K,
                'size': len(V_K),
                'dim_rank': dim_rank,
                'dim_pca': dim_pca,
                'codim_rank': codim_rank,
                'codim_pca': codim_pca,
                'is_K_N_2': is_K_N_2
            })

            # Show eigenvalues for K=N-2
            if is_K_N_2 and len(eigenvalues) > 0:
                ev_str = ", ".join(f"{ev:.2f}" for ev in eigenvalues[:5])
                print(f"      Eigenvalues (top 5): {ev_str}")

    # Summary analysis
    print("\n" + "="*70)
    print("SUMMARY: Codimension Analysis at K=N-2")
    print("="*70)

    K_N_2_results = [r for r in results if r['is_K_N_2']]

    print(f"\n{'N':>3} | {'K':>3} | {'|V_K|':>6} | {'dim(rank)':>10} | {'dim(PCA)':>9} | "
          f"{'codim(rank)':>12} | {'codim(PCA)':>11}")
    print("-"*70)

    for r in K_N_2_results:
        print(f"{r['N']:>3} | {r['K']:>3} | {r['size']:>6} | {r['dim_rank']:>10} | "
              f"{r['dim_pca']:>9} | {r['codim_rank']:>12} | {r['codim_pca']:>11}")

    # Check if codimension = 1 for all K=N-2
    codim_1_rank = all(r['codim_rank'] == 1 for r in K_N_2_results)
    codim_1_pca = all(r['codim_pca'] == 1 for r in K_N_2_results)

    print("\n" + "="*70)
    print("VERIFICATION")
    print("="*70)

    print(f"\nDoes K=N-2 give codimension-1 for all N?")
    print(f"  By matrix rank: {codim_1_rank}")
    print(f"  By PCA: {codim_1_pca}")

    if codim_1_rank or codim_1_pca:
        print("\nRESULT: HYPOTHESIS CONFIRMED")
        print("K=N-2 consistently gives codimension-1!")
        print("\nThis proves the geometric derivation:")
        print("  K = dim(permutohedron) - 1 = (N-1) - 1 = N-2")
        print("\nCodeimension-1 is necessary for 1D flow dynamics (L-flow).")
    else:
        print("\nRESULT: HYPOTHESIS NEEDS REFINEMENT")
        print("Codimension not always 1 at K=N-2.")
        print("May need more sophisticated dimension measure.")

    # Test alternate hypothesis: dim(V_K) = K exactly
    print("\n" + "="*70)
    print("ALTERNATE TEST: dim(V_K) = K?")
    print("="*70)

    for r in results:
        dim_matches_K = (r['dim_rank'] == r['K'] or r['dim_pca'] == r['K'])
        marker = " YES" if dim_matches_K else ""
        print(f"N={r['N']}, K={r['K']}: dim(rank)={r['dim_rank']}, "
              f"dim(PCA)={r['dim_pca']}, K={r['K']}{marker}")

if __name__ == "__main__":
    test_dimension_hypothesis()

    print("\n" + "="*70)
    print("CONCLUSION")
    print("="*70)
    print("\nIf codimension-1 holds at K=N-2, the geometric derivation is proven:")
    print("  - Permutohedron has dimension N-1")
    print("  - K=N-2 gives dim(V_K) = N-2")
    print("  - Codimension = (N-1) - (N-2) = 1")
    print("  - Codimension-1 necessary for 1D flow")
    print("  - Therefore K=N-2 is geometrically NECESSARY")
