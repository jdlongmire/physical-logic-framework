#!/usr/bin/env python3
"""
Quick Diagnostic Tests for K=N-2 Uniqueness

Tests 5 hypotheses to identify which might uniquely determine K=N-2
"""

import numpy as np
from itertools import permutations
from collections import defaultdict
import networkx as nx

def inversion_count(perm):
    """Count inversions"""
    inv = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                inv += 1
    return inv

def adjacent_transposition_distance(perm1, perm2):
    """Count adjacent transpositions needed to transform perm1 to perm2"""
    # This is just the inversion count difference for adjacent perms
    # For general case, need to check if they differ by one adjacent swap
    p1_list = list(perm1)
    p2_list = list(perm2)

    for i in range(len(p1_list) - 1):
        if (p1_list[i] == p2_list[i+1] and
            p1_list[i+1] == p2_list[i] and
            p1_list[:i] == p2_list[:i] and
            p1_list[i+2:] == p2_list[i+2:]):
            return True
    return False

def get_V_K(N, K):
    """Get all permutations with h <= K"""
    perms = list(permutations(range(N)))
    h = {perm: inversion_count(perm) for perm in perms}
    return {perm for perm in perms if h[perm] <= K}

def get_generators(N):
    """Get all N-1 adjacent transposition generators"""
    generators = []
    identity = tuple(range(N))

    for i in range(N-1):
        gen = list(identity)
        gen[i], gen[i+1] = gen[i+1], gen[i]
        generators.append(tuple(gen))

    return generators

# Test 1: Generator Containment Hypothesis
def test_generator_containment(N):
    """
    Hypothesis: K=N-2 is minimal K such that V_K contains all generators
    """
    print(f"\n{'='*60}")
    print(f"TEST 1: Generator Containment (N={N})")
    print(f"{'='*60}")

    generators = get_generators(N)
    print(f"Number of generators: {len(generators)} (should be N-1 = {N-1})")
    print(f"Generators (adjacent transpositions):")
    for i, g in enumerate(generators):
        h_g = inversion_count(g)
        print(f"  tau_{i+1} = {g}, h = {h_g}")

    # Test for different K values
    print(f"\nTesting which K contains all generators:")
    for K in range(0, N):
        V_K = get_V_K(N, K)
        contains_all = all(g in V_K for g in generators)
        symbol = "YES" if contains_all else "NO"
        print(f"  K={K}: {symbol} ({len([g for g in generators if g in V_K])}/{len(generators)} generators)")

    # Check specific hypothesis: K=N-2 is minimal?
    V_N_2 = get_V_K(N, N-2)
    V_N_3 = get_V_K(N, N-3) if N >= 4 else set()

    contains_all_at_N_2 = all(g in V_N_2 for g in generators)
    contains_all_at_N_3 = all(g in V_N_3 for g in generators) if N >= 4 else False

    result = {
        'N': N,
        'num_generators': len(generators),
        'all_in_V_N-2': contains_all_at_N_2,
        'all_in_V_N-3': contains_all_at_N_3 if N >= 4 else None,
        'minimal_K': N-2 if contains_all_at_N_2 and not contains_all_at_N_3 else "Unknown"
    }

    print(f"\nResult: All generators in V_{{N-2}}? {contains_all_at_N_2}")
    if N >= 4:
        print(f"        All generators in V_{{N-3}}? {contains_all_at_N_3}")

    return result

# Test 2: Dimension Matching Hypothesis
def test_dimension_matching(N):
    """
    Hypothesis: K = dim(permutohedron) - 1 = (N-1) - 1 = N-2
    """
    print(f"\n{'='*60}")
    print(f"TEST 2: Dimension Matching (N={N})")
    print(f"{'='*60}")

    dim_permutohedron = N - 1
    K_predicted = dim_permutohedron - 1

    print(f"Dimension of permutohedron Π_{{N-1}}: {dim_permutohedron}")
    print(f"Predicted K = dim - 1: {K_predicted}")
    print(f"Actual K from empirics: {N-2}")
    print(f"Match? {K_predicted == N-2}")

    # Check if |V_K| relates to dim
    V_K = get_V_K(N, N-2)
    print(f"\n|V_{{N-2}}| = {len(V_K)}")
    print(f"Relation to dimension: |V|/dim = {len(V_K)/dim_permutohedron:.2f}")

    return {
        'N': N,
        'dim': dim_permutohedron,
        'K_from_dim': K_predicted,
        'K_empirical': N-2,
        'matches': K_predicted == N-2
    }

# Test 3: Cayley Graph Diameter Hypothesis
def test_graph_diameter(N):
    """
    Hypothesis: K=N-2 gives special diameter property
    """
    print(f"\n{'='*60}")
    print(f"TEST 3: Cayley Graph Diameter (N={N})")
    print(f"{'='*60}")

    # Build Cayley graph for V_K
    def build_cayley_graph(V_K):
        G = nx.Graph()
        G.add_nodes_from(V_K)

        # Add edges for adjacent transpositions
        for perm in V_K:
            for i in range(len(perm)-1):
                # Apply transposition (i, i+1)
                neighbor = list(perm)
                neighbor[i], neighbor[i+1] = neighbor[i+1], neighbor[i]
                neighbor = tuple(neighbor)
                if neighbor in V_K:
                    G.add_edge(perm, neighbor)

        return G

    identity = tuple(range(N))

    # Test for different K values
    print(f"Testing Cayley graph properties for different K:")
    for K in range(1, min(N+1, 6)):  # Limit for computational feasibility
        V_K = get_V_K(N, K)
        if len(V_K) > 1000:  # Skip if too large
            print(f"  K={K}: Skipped (|V_K| = {len(V_K)} too large)")
            continue

        G = build_cayley_graph(V_K)

        # Compute diameter (if connected)
        if nx.is_connected(G):
            diameter = nx.diameter(G)
            avg_path = nx.average_shortest_path_length(G)
        else:
            diameter = "Not connected"
            avg_path = "N/A"

        print(f"  K={K}: |V_K|={len(V_K):4d}, diameter={diameter}, avg_path={avg_path}")

    # Check if K=N-2 has diameter equal to K
    V_N_2 = get_V_K(N, N-2)
    G_N_2 = build_cayley_graph(V_N_2)

    if nx.is_connected(G_N_2):
        diam_N_2 = nx.diameter(G_N_2)
        print(f"\nDiameter of V_{{N-2}}: {diam_N_2}")
        print(f"K = N-2 = {N-2}")
        print(f"Does diameter = K? {diam_N_2 == N-2}")
    else:
        print(f"\nV_{{N-2}} not connected!")

    return {'N': N, 'tested': True}

# Test 4: Exponential Decay Rate Hypothesis
def test_decay_rate(max_N=7):
    """
    Hypothesis: K=N-2 gives unique decay rate alpha
    """
    print(f"\n{'='*60}")
    print(f"TEST 4: Exponential Decay Rate")
    print(f"{'='*60}")

    from math import factorial, log

    # Compute for K=N-2, K=N-3, K=N-1
    N_vals = list(range(3, max_N+1))

    for K_offset in [-1, 0, 1]:  # K=N-3, N-2, N-1
        K_label = f"N{K_offset:+d}" if K_offset != 0 else "N-2"

        rho_vals = []
        for N in N_vals:
            K = N - 2 + K_offset
            if K < 0 or K > N*(N-1)//2:
                continue

            V_K = get_V_K(N, K)
            rho = len(V_K) / factorial(N)
            rho_vals.append((N, rho))

        if len(rho_vals) < 3:
            continue

        # Fit exponential: rho ~ C * exp(-alpha * N)
        N_fit = np.array([x[0] for x in rho_vals])
        rho_fit = np.array([x[1] for x in rho_vals])
        log_rho = np.log(rho_fit)

        coeffs = np.polyfit(N_fit, log_rho, 1)
        alpha = -coeffs[0]
        C = np.exp(coeffs[1])

        print(f"\nK = {K_label}:")
        for N, rho in rho_vals:
            print(f"  N={N}: rho = {rho:.6f}")

        print(f"  Fit: rho ~ {C:.3f} * exp(-{alpha:.3f} * N)")

    return {'tested': True}

# Test 5: Information-Theoretic Optimality
def test_rate_distortion(N):
    """
    Hypothesis: K=N-2 optimizes rate-distortion tradeoff
    """
    print(f"\n{'='*60}")
    print(f"TEST 5: Rate-Distortion (N={N})")
    print(f"{'='*60}")

    max_K = min(N*(N-1)//2, 10)  # Limit for feasibility

    rates = []
    distortions = []

    for K in range(0, max_K+1):
        V_K = get_V_K(N, K)

        # Rate: R = log2(|V_K|)
        rate = np.log2(len(V_K))

        # Distortion: Expected inversion count (assume uniform)
        avg_inversions = np.mean([inversion_count(perm) for perm in V_K])

        rates.append(rate)
        distortions.append(avg_inversions)

        marker = " <-- K=N-2" if K == N-2 else ""
        print(f"  K={K:2d}: R={rate:5.2f} bits, D={avg_inversions:5.2f}{marker}")

    # Check if K=N-2 is at "knee" of curve
    K_N_2 = N - 2
    if K_N_2 < len(rates):
        print(f"\nAt K=N-2={K_N_2}:")
        print(f"  Rate: {rates[K_N_2]:.2f} bits")
        print(f"  Distortion: {distortions[K_N_2]:.2f}")

    return {'N': N, 'rates': rates, 'distortions': distortions}

# Main execution
if __name__ == "__main__":
    print("="*60)
    print("K(N)=N-2 UNIQUENESS HYPOTHESIS TESTS")
    print("="*60)
    print("\nTesting 5 hypotheses for why K=N-2 is uniquely selected\n")

    # Run tests for N=3,4,5
    for N in [3, 4, 5]:
        print(f"\n{'#'*60}")
        print(f"# N = {N}")
        print(f"{'#'*60}")

        test_generator_containment(N)
        test_dimension_matching(N)

        if N <= 4:  # Diameter test only for small N
            test_graph_diameter(N)

        if N <= 5:
            test_rate_distortion(N)

    # Decay rate test across multiple N
    test_decay_rate(max_N=7)

    print(f"\n{'='*60}")
    print("SUMMARY: Which hypothesis looks most promising?")
    print("="*60)
    print("\n1. Generator Containment: Check if K=N-2 is minimal for all generators")
    print("2. Dimension Matching: K = dim - 1 is exact match!")
    print("3. Graph Diameter: Does diameter have special property?")
    print("4. Decay Rate: Is alpha unique for K=N-2?")
    print("5. Rate-Distortion: Is K=N-2 at optimal tradeoff point?")
    print("\nRun this script to see which direction is most promising!")
