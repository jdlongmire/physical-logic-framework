#!/usr/bin/env python3
"""
Test whether S_N structure approaches Lorentz group SO(3,1) as N increases

This script implements three complementary tests:
1. Spectral analysis: Graph Laplacian eigenvalue distribution
2. Symmetry dimension: Count of independent generators
3. Light cone structure: Causal relationships in constraint space

Usage:
    python test_lorentz_convergence.py --N_max=10 --verbose
"""

import numpy as np
import networkx as nx
from itertools import permutations
import matplotlib.pyplot as plt
from scipy.spatial.distance import squareform, pdist
from scipy.stats import kstest
import argparse
import json
from datetime import datetime

def compute_inversion_count(perm):
    """Compute inversion count h(σ)"""
    n = len(perm)
    count = 0
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                count += 1
    return count

def build_permutohedron(N, K=None):
    """
    Build Cayley graph of S_N with constraint h(σ) ≤ K

    Returns:
        G: NetworkX graph
        valid_nodes: List of permutations satisfying constraint
        node_to_h: Dict mapping nodes to inversion counts
    """
    if K is None:
        K = N - 2

    # Generate all permutations
    all_perms = list(permutations(range(1, N+1)))

    # Compute inversion counts
    node_to_h = {p: compute_inversion_count(p) for p in all_perms}

    # Filter by constraint
    valid_nodes = [p for p in all_perms if node_to_h[p] <= K]

    # Build graph (only valid nodes)
    G = nx.Graph()
    G.add_nodes_from(valid_nodes)

    # Add edges for adjacent transpositions
    for p in valid_nodes:
        for i in range(N-1):
            q = list(p)
            q[i], q[i+1] = q[i+1], q[i]
            q = tuple(q)
            if q in valid_nodes:
                G.add_edge(p, q)

    return G, valid_nodes, node_to_h

def spectral_analysis(G, N):
    """
    Test 1: Spectral properties of graph Laplacian

    Theory: Eigenvalues of Laplacian on continuous manifold have
    characteristic distribution (Weyl's law). If permutohedron
    approaches smooth manifold, eigenvalue distribution should
    approach continuous behavior.

    Returns:
        dict with eigenvalue statistics
    """
    # Compute graph Laplacian
    L = nx.laplacian_matrix(G).toarray()

    # Eigenvalues (sorted)
    eigenvalues = np.linalg.eigvalsh(L)
    eigenvalues = np.sort(eigenvalues)

    # Weyl's law for d-dimensional manifold:
    # λ_k ~ (k/V)^(2/d) for large k
    # For N=4 → d=3, we expect cubic growth

    d_expected = N - 1  # Expected dimension
    n_nodes = len(G.nodes())

    # Fit power law to eigenvalue growth
    k_values = np.arange(1, len(eigenvalues) + 1)

    # Remove zero eigenvalue (connected component)
    if eigenvalues[0] < 1e-10:
        k_values = k_values[1:]
        eigenvalues = eigenvalues[1:]

    # Log-log fit: log(λ) ~ (2/d) log(k) + const
    if len(eigenvalues) > 10:
        log_k = np.log(k_values[:len(eigenvalues)])
        log_lambda = np.log(eigenvalues + 1e-10)  # Avoid log(0)

        # Linear regression
        coeffs = np.polyfit(log_k, log_lambda, 1)
        estimated_dimension = 2 / coeffs[0] if coeffs[0] > 0 else np.nan
    else:
        estimated_dimension = np.nan

    # Spectral gap (indicator of geometric structure)
    spectral_gap = eigenvalues[1] - eigenvalues[0] if len(eigenvalues) > 1 else 0

    return {
        'eigenvalues': eigenvalues.tolist(),
        'n_eigenvalues': len(eigenvalues),
        'max_eigenvalue': float(np.max(eigenvalues)),
        'spectral_gap': float(spectral_gap),
        'estimated_dimension': float(estimated_dimension),
        'expected_dimension': d_expected
    }

def symmetry_dimension(G, valid_nodes, N):
    """
    Test 2: Count effective dimension of symmetry group

    Theory: SO(3,1) has dimension 6 (3 boosts + 3 rotations)

    Method: Count linearly independent "infinitesimal" transformations
    by analyzing graph automorphisms and near-automorphisms

    Returns:
        dict with symmetry analysis
    """
    # Exact automorphisms
    automorphism_group = nx.algorithms.isomorphism.GraphMatcher(G, G)
    n_automorphisms = sum(1 for _ in automorphism_group.isomorphisms_iter())

    # For permutohedron, automorphisms correspond to permutation relabeling
    # Expected: S_N has N! automorphisms, but constraint may reduce

    # Estimate "dimension" from automorphism group size
    # dim(G) ~ log(|Aut(G)|) / log(N)  (heuristic)
    if n_automorphisms > 1:
        symmetry_dimension_est = np.log(n_automorphisms) / np.log(N) if N > 1 else 0
    else:
        symmetry_dimension_est = 0

    # SO(3,1) has dim = 6, so we expect convergence toward 6 for large N
    # But this is very rough - mainly checking if dimension stabilizes

    return {
        'n_automorphisms': int(n_automorphisms),
        'symmetry_dimension_estimate': float(symmetry_dimension_est),
        'expected_lorentz_dimension': 6
    }

def light_cone_structure(G, valid_nodes, node_to_h, N):
    """
    Test 3: Check if constraint creates light-cone-like structure

    Theory: In Lorentz geometry, events are causally related if
    ds² < 0 (timelike separated). The constraint h ≤ K should
    create cone-like causal structure.

    Method:
    - Time direction = L-Flow (decreasing h)
    - Space directions = transpositions preserving h
    - Light cone = boundary h = K

    Returns:
        dict with causal structure analysis
    """
    # Identify "timelike" vs "spacelike" edges
    timelike_edges = []
    spacelike_edges = []

    for u, v in G.edges():
        h_u = node_to_h[u]
        h_v = node_to_h[v]

        if h_u != h_v:
            # Different h → timelike (L-Flow direction)
            timelike_edges.append((u, v, abs(h_u - h_v)))
        else:
            # Same h → spacelike (transposition at constant h)
            spacelike_edges.append((u, v))

    # Ratio of timelike to spacelike
    n_timelike = len(timelike_edges)
    n_spacelike = len(spacelike_edges)
    total_edges = n_timelike + n_spacelike

    if total_edges > 0:
        timelike_fraction = n_timelike / total_edges
        spacelike_fraction = n_spacelike / total_edges
    else:
        timelike_fraction = 0
        spacelike_fraction = 0

    # For Minkowski space: expect ~1/4 timelike, ~3/4 spacelike (1 time, 3 space)
    # But this is VERY rough - topology matters

    # Check if constraint boundary h=K acts like "light cone"
    boundary_nodes = [p for p in valid_nodes if node_to_h[p] == N-2]
    n_boundary = len(boundary_nodes)
    n_interior = len(valid_nodes) - n_boundary

    # In Lorentz: light cone is boundary, interior is timelike region
    boundary_fraction = n_boundary / len(valid_nodes) if len(valid_nodes) > 0 else 0

    return {
        'n_timelike_edges': n_timelike,
        'n_spacelike_edges': n_spacelike,
        'timelike_fraction': float(timelike_fraction),
        'spacelike_fraction': float(spacelike_fraction),
        'expected_timelike_fraction': 0.25,  # 1/4 for (1+3)D
        'n_boundary_nodes': n_boundary,
        'n_interior_nodes': n_interior,
        'boundary_fraction': float(boundary_fraction)
    }

def convergence_metric(results):
    """
    Compute overall convergence score from all three tests

    Returns:
        score: 0-1, where 1 = perfect convergence to Lorentz
    """
    scores = []

    # Test 1: Dimension estimate
    if 'estimated_dimension' in results['spectral'] and not np.isnan(results['spectral']['estimated_dimension']):
        expected = results['spectral']['expected_dimension']
        estimated = results['spectral']['estimated_dimension']
        # For N=4, expect d=3; score based on closeness
        dim_score = 1.0 - min(abs(estimated - expected) / expected, 1.0)
        scores.append(dim_score)

    # Test 2: Symmetry dimension
    # This is very heuristic - just check if it's non-zero and growing
    sym_dim = results['symmetry']['symmetry_dimension_estimate']
    if sym_dim > 0:
        # SO(3,1) has dim 6, but we expect much larger for finite groups
        # Just reward growth
        scores.append(min(sym_dim / 10, 1.0))  # Normalize

    # Test 3: Light cone structure
    # Expect ~1/4 timelike for (1+3)D
    timelike_frac = results['light_cone']['timelike_fraction']
    expected_frac = 0.25
    cone_score = 1.0 - min(abs(timelike_frac - expected_frac) / expected_frac, 1.0)
    scores.append(cone_score)

    # Overall score (average)
    if len(scores) > 0:
        return np.mean(scores)
    else:
        return 0.0

def run_convergence_test(N_values, verbose=True):
    """
    Run all three tests for each N value

    Returns:
        results: dict with all test results
    """
    results_by_N = {}

    for N in N_values:
        if verbose:
            print(f"\n{'='*60}")
            print(f"Testing N={N} (K={N-2})")
            print(f"{'='*60}")

        # Build constrained permutohedron
        K = N - 2
        G, valid_nodes, node_to_h = build_permutohedron(N, K)

        n_total = len(list(permutations(range(1, N+1))))
        n_valid = len(valid_nodes)

        if verbose:
            print(f"Total permutations: {n_total}")
            print(f"Valid states (h<={K}): {n_valid} ({100*n_valid/n_total:.2f}%)")
            print(f"Graph edges: {G.number_of_edges()}")

        # Run three tests
        spectral = spectral_analysis(G, N)
        symmetry = symmetry_dimension(G, valid_nodes, N)
        light_cone = light_cone_structure(G, valid_nodes, node_to_h, N)

        # Combine results
        result = {
            'N': N,
            'K': K,
            'n_total_perms': n_total,
            'n_valid_states': n_valid,
            'feasibility_ratio': n_valid / n_total,
            'n_edges': G.number_of_edges(),
            'spectral': spectral,
            'symmetry': symmetry,
            'light_cone': light_cone
        }

        # Compute convergence score
        result['convergence_score'] = convergence_metric(result)

        if verbose:
            print(f"\nTest Results:")
            print(f"  Spectral dimension estimate: {spectral['estimated_dimension']:.2f} (expected: {spectral['expected_dimension']})")
            print(f"  Symmetry dimension estimate: {symmetry['symmetry_dimension_estimate']:.2f} (Lorentz: 6)")
            print(f"  Timelike edge fraction: {light_cone['timelike_fraction']:.3f} (expected: ~0.25)")
            print(f"  CONVERGENCE SCORE: {result['convergence_score']:.3f}")

        results_by_N[N] = result

    return results_by_N

def plot_convergence(results_by_N, output_dir='paper/figures/outputs'):
    """Generate convergence plots"""
    import os
    os.makedirs(output_dir, exist_ok=True)

    N_values = sorted(results_by_N.keys())

    # Create figure with 4 subplots
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Plot 1: Dimension convergence
    ax1 = axes[0, 0]
    estimated_dims = [results_by_N[N]['spectral']['estimated_dimension'] for N in N_values]
    expected_dims = [results_by_N[N]['spectral']['expected_dimension'] for N in N_values]

    ax1.plot(N_values, estimated_dims, 'o-', label='Estimated from spectrum', linewidth=2, markersize=8)
    ax1.plot(N_values, expected_dims, 's--', label='Expected (N-1)', linewidth=2, markersize=8)
    ax1.axhline(y=3, color='red', linestyle=':', label='Target (3D space)', linewidth=2)
    ax1.set_xlabel('N', fontsize=11, fontweight='bold')
    ax1.set_ylabel('Effective Dimension', fontsize=11, fontweight='bold')
    ax1.set_title('Dimension Estimate from Spectral Analysis', fontsize=12, fontweight='bold')
    ax1.legend(fontsize=9)
    ax1.grid(alpha=0.3)

    # Plot 2: Light cone structure
    ax2 = axes[0, 1]
    timelike_fracs = [results_by_N[N]['light_cone']['timelike_fraction'] for N in N_values]
    ax2.plot(N_values, timelike_fracs, 'o-', label='Observed', linewidth=2, markersize=8, color='blue')
    ax2.axhline(y=0.25, color='red', linestyle='--', label='Expected (1/4 for 1+3D)', linewidth=2)
    ax2.set_xlabel('N', fontsize=11, fontweight='bold')
    ax2.set_ylabel('Timelike Edge Fraction', fontsize=11, fontweight='bold')
    ax2.set_title('Causal Structure: Timelike vs Spacelike', fontsize=12, fontweight='bold')
    ax2.legend(fontsize=9)
    ax2.grid(alpha=0.3)
    ax2.set_ylim(0, 0.6)

    # Plot 3: Convergence score
    ax3 = axes[1, 0]
    conv_scores = [results_by_N[N]['convergence_score'] for N in N_values]
    ax3.plot(N_values, conv_scores, 'o-', linewidth=2, markersize=8, color='green')
    ax3.axhline(y=1.0, color='red', linestyle='--', label='Perfect convergence', linewidth=2)
    ax3.set_xlabel('N', fontsize=11, fontweight='bold')
    ax3.set_ylabel('Convergence Score', fontsize=11, fontweight='bold')
    ax3.set_title('Overall Convergence to Lorentz Structure', fontsize=12, fontweight='bold')
    ax3.legend(fontsize=9)
    ax3.grid(alpha=0.3)
    ax3.set_ylim(0, 1.2)

    # Plot 4: Symmetry dimension
    ax4 = axes[1, 1]
    sym_dims = [results_by_N[N]['symmetry']['symmetry_dimension_estimate'] for N in N_values]
    ax4.plot(N_values, sym_dims, 'o-', linewidth=2, markersize=8, color='purple')
    ax4.axhline(y=6, color='red', linestyle='--', label='SO(3,1) dimension', linewidth=2)
    ax4.set_xlabel('N', fontsize=11, fontweight='bold')
    ax4.set_ylabel('Symmetry Dimension', fontsize=11, fontweight='bold')
    ax4.set_title('Effective Symmetry Group Dimension', fontsize=12, fontweight='bold')
    ax4.legend(fontsize=9)
    ax4.grid(alpha=0.3)

    plt.suptitle('S_N → SO(3,1) Convergence Analysis (K=N-2)',
                 fontsize=15, fontweight='bold', y=0.995)
    plt.tight_layout()

    # Save
    png_path = os.path.join(output_dir, 'figure_lorentz_convergence.png')
    svg_path = os.path.join(output_dir, 'figure_lorentz_convergence.svg')
    plt.savefig(png_path, dpi=300, bbox_inches='tight')
    plt.savefig(svg_path, format='svg', bbox_inches='tight')
    plt.close()

    print(f"\n[OK] Saved convergence plots: {png_path}, {svg_path}")

def main():
    parser = argparse.ArgumentParser(description='Test S_N to SO(3,1) convergence')
    parser.add_argument('--N_max', type=int, default=8, help='Maximum N to test (default: 8)')
    parser.add_argument('--N_min', type=int, default=3, help='Minimum N to test (default: 3)')
    parser.add_argument('--verbose', action='store_true', help='Verbose output')
    parser.add_argument('--output', type=str, default='data/lorentz_convergence_results.json',
                       help='Output JSON file')

    args = parser.parse_args()

    # Run tests
    N_values = list(range(args.N_min, args.N_max + 1))

    print("="*60)
    print("S_N -> SO(3,1) Convergence Test")
    print("="*60)
    print(f"Testing N={args.N_min} to {args.N_max}")
    print(f"Constraint: K=N-2 (Born rule threshold)")
    print("="*60)

    results = run_convergence_test(N_values, verbose=args.verbose)

    # Save results
    output_data = {
        'metadata': {
            'date': datetime.now().isoformat(),
            'N_range': [args.N_min, args.N_max],
            'constraint': 'K=N-2'
        },
        'results': results
    }

    import os
    os.makedirs(os.path.dirname(args.output), exist_ok=True)
    with open(args.output, 'w') as f:
        json.dump(output_data, f, indent=2)

    print(f"\n[OK] Results saved: {args.output}")

    # Generate plots
    plot_convergence(results)

    # Summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)

    final_N = args.N_max
    final_score = results[final_N]['convergence_score']

    print(f"Final convergence score (N={final_N}): {final_score:.3f}")

    if final_score > 0.7:
        print("\n[STRONG] STRONG EVIDENCE: S_N structure shows clear convergence toward Lorentz")
        print("  Recommendation: Write CT integration confidently")
    elif final_score > 0.4:
        print("\n[MODERATE] Some convergence visible, more investigation needed")
        print("  Recommendation: Frame as 'preliminary evidence' + future work")
    else:
        print("\n[WEAK] No clear convergence observed")
        print("  Recommendation: Keep CT integration conceptual only, acknowledge limitation")

    print("="*60)

if __name__ == "__main__":
    main()
