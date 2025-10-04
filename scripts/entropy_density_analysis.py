#!/usr/bin/env python3
"""
Entropy Density Analysis: Validating K(N) = N-2 Geometric Hypothesis

This script tests the geometric hypothesis that K(N) = N-2 maximizes
the entropy density H/(N-1) on the permutohedron.

Key Predictions:
1. Entropy density log|V_K|/(N-1) should peak at K=N-2
2. Valid permutation graph should transition to connectivity at K=N-2
3. Pattern should hold for N=3..10+

Based on expert consultation (Gemini, ChatGPT) synthesis.
"""

import numpy as np
import itertools
import matplotlib.pyplot as plt
import pandas as pd
from collections import defaultdict
import networkx as nx
import os
import json
from datetime import datetime

def inversion_count(perm):
    """Compute inversion count h(sigma)"""
    count = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                count += 1
    return count

def count_valid_perms(N, K):
    """Count permutations with h(sigma) <= K"""
    all_perms = itertools.permutations(range(N))
    count = 0
    for perm in all_perms:
        if inversion_count(perm) <= K:
            count += 1
    return count

def adjacent_transposition(perm, i):
    """Apply adjacent transposition at position i"""
    perm_list = list(perm)
    perm_list[i], perm_list[i+1] = perm_list[i+1], perm_list[i]
    return tuple(perm_list)

def build_permutation_graph(valid_perms):
    """Build graph with valid perms as vertices, adjacent transpositions as edges"""
    G = nx.Graph()

    # Add vertices
    for perm in valid_perms:
        G.add_node(perm)

    # Add edges (adjacent transpositions)
    for perm in valid_perms:
        N = len(perm)
        for i in range(N-1):
            neighbor = adjacent_transposition(perm, i)
            if neighbor in valid_perms:
                G.add_edge(perm, neighbor)

    return G

def analyze_connectivity(G):
    """Analyze graph connectivity properties"""
    if G.number_of_nodes() == 0:
        return {
            'is_connected': False,
            'num_components': 0,
            'largest_component_size': 0,
            'largest_component_fraction': 0.0,
            'avg_clustering': 0.0,
            'diameter': float('inf')
        }

    # Connectivity
    is_connected = nx.is_connected(G)
    num_components = nx.number_connected_components(G)

    # Component analysis
    if num_components > 0:
        components = list(nx.connected_components(G))
        largest_component_size = max(len(c) for c in components)
        largest_component_fraction = largest_component_size / G.number_of_nodes()
    else:
        largest_component_size = 0
        largest_component_fraction = 0.0

    # Clustering
    avg_clustering = nx.average_clustering(G) if G.number_of_nodes() > 0 else 0.0

    # Diameter (for connected graphs)
    if is_connected and G.number_of_nodes() > 1:
        diameter = nx.diameter(G)
    else:
        diameter = float('inf')

    return {
        'is_connected': is_connected,
        'num_components': num_components,
        'largest_component_size': largest_component_size,
        'largest_component_fraction': largest_component_fraction,
        'avg_clustering': avg_clustering,
        'diameter': diameter
    }

def entropy_density_analysis(N_max=8):
    """
    Main analysis: compute entropy density for N=3..N_max, all K

    Tests geometric hypothesis: entropy density peaks at K=N-2
    """

    print("="*80)
    print("ENTROPY DENSITY ANALYSIS: Validating K(N) = N-2 Geometric Hypothesis")
    print("="*80)

    results = []

    for N in range(3, N_max + 1):
        print(f"\nAnalyzing N={N}...")

        max_inversions = N * (N - 1) // 2

        for K in range(0, max_inversions + 1):
            # Count valid permutations
            V_K = count_valid_perms(N, K)

            if V_K == 0:
                continue

            # Entropy density
            entropy = np.log(V_K)
            entropy_density = entropy / (N - 1)  # Normalize by permutohedron dimension

            # Check if this is the K=N-2 point
            is_predicted = (K == N - 2)

            results.append({
                'N': N,
                'K': K,
                'V_K': V_K,
                'entropy': entropy,
                'entropy_density': entropy_density,
                'is_K_N_minus_2': is_predicted,
                'dimension': N - 1
            })

            if K <= N or K == max_inversions:  # Print key points
                marker = " <- K=N-2" if is_predicted else ""
                print(f"  K={K:2d}: |V|={V_K:5d}, H={entropy:.3f}, H/(N-1)={entropy_density:.4f}{marker}")

    return pd.DataFrame(results)

def connectivity_analysis(N_max=6):
    """
    Analyze connectivity transition as K increases

    Tests: K=N-2 is connectivity transition point
    """

    print("\n" + "="*80)
    print("CONNECTIVITY ANALYSIS: Graph Structure of Valid Permutations")
    print("="*80)

    connectivity_results = []

    for N in range(3, N_max + 1):
        print(f"\nAnalyzing connectivity for N={N}...")

        # Generate all permutations
        all_perms = list(itertools.permutations(range(N)))

        # Group by inversion count
        by_inversions = defaultdict(list)
        for perm in all_perms:
            h = inversion_count(perm)
            by_inversions[h].append(perm)

        max_inversions = N * (N - 1) // 2

        for K in range(0, min(N + 3, max_inversions + 1)):  # Focus on K near N-2
            # Get valid permutations
            valid_perms = []
            for h in range(K + 1):
                valid_perms.extend(by_inversions[h])

            if len(valid_perms) == 0:
                continue

            # Build graph
            G = build_permutation_graph(valid_perms)

            # Analyze connectivity
            conn_stats = analyze_connectivity(G)

            is_predicted = (K == N - 2)

            connectivity_results.append({
                'N': N,
                'K': K,
                'num_vertices': G.number_of_nodes(),
                'num_edges': G.number_of_edges(),
                'is_connected': conn_stats['is_connected'],
                'num_components': conn_stats['num_components'],
                'largest_component_fraction': conn_stats['largest_component_fraction'],
                'avg_clustering': conn_stats['avg_clustering'],
                'diameter': conn_stats['diameter'],
                'is_K_N_minus_2': is_predicted
            })

            marker = " <- K=N-2" if is_predicted else ""
            conn_str = "CONNECTED" if conn_stats['is_connected'] else f"{conn_stats['num_components']} components"
            print(f"  K={K}: vertices={G.number_of_nodes():3d}, {conn_str}{marker}")

    return pd.DataFrame(connectivity_results)

def visualize_results(entropy_df, connectivity_df):
    """Create comprehensive visualizations"""

    print("\n" + "="*80)
    print("GENERATING VISUALIZATIONS")
    print("="*80)

    os.makedirs('./outputs', exist_ok=True)

    # Figure 1: Entropy Density Analysis
    fig = plt.figure(figsize=(16, 10))

    # Plot 1: Entropy density vs K for each N
    ax1 = plt.subplot(2, 3, 1)
    for N in sorted(entropy_df['N'].unique()):
        data_n = entropy_df[entropy_df['N'] == N]
        ax1.plot(data_n['K'], data_n['entropy_density'], 'o-', label=f'N={N}', alpha=0.7)

        # Mark K=N-2 point
        k_n_minus_2 = N - 2
        point = data_n[data_n['K'] == k_n_minus_2]
        if not point.empty:
            ax1.plot(point['K'], point['entropy_density'], 'r*', markersize=15)

    ax1.set_xlabel('Constraint threshold K')
    ax1.set_ylabel('Entropy density H/(N-1)')
    ax1.set_title('Entropy Density vs K')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Plot 2: Does H/(N-1) peak at K=N-2?
    ax2 = plt.subplot(2, 3, 2)
    peak_analysis = []
    for N in sorted(entropy_df['N'].unique()):
        data_n = entropy_df[entropy_df['N'] == N]
        max_density = data_n['entropy_density'].max()
        k_at_max = data_n[data_n['entropy_density'] == max_density]['K'].iloc[0]
        predicted_k = N - 2

        peak_analysis.append({
            'N': N,
            'K_at_peak': k_at_max,
            'K_predicted': predicted_k,
            'matches': k_at_max == predicted_k
        })

    peak_df = pd.DataFrame(peak_analysis)
    x = peak_df['N']
    ax2.plot(x, peak_df['K_at_peak'], 'bo-', label='Actual peak', linewidth=2)
    ax2.plot(x, peak_df['K_predicted'], 'r^--', label='K=N-2 prediction', linewidth=2)
    ax2.set_xlabel('System size N')
    ax2.set_ylabel('K at entropy density peak')
    ax2.set_title('Peak Location Validation')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    # Plot 3: Number of valid permutations vs K
    ax3 = plt.subplot(2, 3, 3)
    for N in sorted(entropy_df['N'].unique()):
        data_n = entropy_df[entropy_df['N'] == N]
        ax3.semilogy(data_n['K'], data_n['V_K'], 'o-', label=f'N={N}', alpha=0.7)

        # Mark K=N-2
        k_n_minus_2 = N - 2
        point = data_n[data_n['K'] == k_n_minus_2]
        if not point.empty:
            ax3.plot(point['K'], point['V_K'], 'r*', markersize=15)

    ax3.set_xlabel('Constraint threshold K')
    ax3.set_ylabel('|V_K| (log scale)')
    ax3.set_title('Valid Permutations vs K')
    ax3.legend()
    ax3.grid(True, alpha=0.3)

    # Plot 4: Connectivity transition
    ax4 = plt.subplot(2, 3, 4)
    for N in sorted(connectivity_df['N'].unique()):
        data_n = connectivity_df[connectivity_df['N'] == N]
        ax4.plot(data_n['K'], data_n['largest_component_fraction'], 'o-', label=f'N={N}', alpha=0.7)

        # Mark K=N-2
        k_n_minus_2 = N - 2
        point = data_n[data_n['K'] == k_n_minus_2]
        if not point.empty:
            ax4.plot(point['K'], point['largest_component_fraction'], 'r*', markersize=15)

    ax4.axhline(y=1.0, color='k', linestyle='--', alpha=0.3, label='Fully connected')
    ax4.set_xlabel('Constraint threshold K')
    ax4.set_ylabel('Largest component fraction')
    ax4.set_title('Connectivity Transition')
    ax4.legend()
    ax4.grid(True, alpha=0.3)

    # Plot 5: Number of components
    ax5 = plt.subplot(2, 3, 5)
    for N in sorted(connectivity_df['N'].unique()):
        data_n = connectivity_df[connectivity_df['N'] == N]
        ax5.plot(data_n['K'], data_n['num_components'], 'o-', label=f'N={N}', alpha=0.7)

        # Mark K=N-2
        k_n_minus_2 = N - 2
        point = data_n[data_n['K'] == k_n_minus_2]
        if not point.empty:
            ax5.plot(point['K'], point['num_components'], 'r*', markersize=15)

    ax5.set_xlabel('Constraint threshold K')
    ax5.set_ylabel('Number of components')
    ax5.set_title('Graph Fragmentation')
    ax5.legend()
    ax5.grid(True, alpha=0.3)

    # Plot 6: Diameter (connectivity quality)
    ax6 = plt.subplot(2, 3, 6)
    for N in sorted(connectivity_df['N'].unique()):
        data_n = connectivity_df[connectivity_df['N'] == N]
        # Filter out infinite diameters
        data_finite = data_n[data_n['diameter'] != float('inf')]
        if not data_finite.empty:
            ax6.plot(data_finite['K'], data_finite['diameter'], 'o-', label=f'N={N}', alpha=0.7)

            # Mark K=N-2
            k_n_minus_2 = N - 2
            point = data_finite[data_finite['K'] == k_n_minus_2]
            if not point.empty:
                ax6.plot(point['K'], point['diameter'], 'r*', markersize=15)

    ax6.set_xlabel('Constraint threshold K')
    ax6.set_ylabel('Graph diameter')
    ax6.set_title('Connectivity Quality (Diameter)')
    ax6.legend()
    ax6.grid(True, alpha=0.3)

    plt.suptitle('K(N)=N-2 Geometric Hypothesis Validation\n(Red stars = K=N-2 predictions)',
                 fontsize=14, fontweight='bold')
    plt.tight_layout()

    output_path = './outputs/entropy_density_validation.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"\nSaved comprehensive visualization: {output_path}")

    return peak_df

def validate_hypothesis(entropy_df, connectivity_df, peak_df):
    """
    Statistical validation of geometric hypothesis
    """

    print("\n" + "="*80)
    print("HYPOTHESIS VALIDATION SUMMARY")
    print("="*80)

    # Test 1: Entropy density peaks at K=N-2
    n_values = len(peak_df)
    n_matches = peak_df['matches'].sum()
    peak_success_rate = n_matches / n_values if n_values > 0 else 0

    print(f"\nTest 1: Entropy Density Peak Location")
    print(f"  Hypothesis: H/(N-1) maximized at K=N-2")
    print(f"  Results: {n_matches}/{n_values} cases match ({peak_success_rate:.1%})")
    print(f"  Status: {'VALIDATED' if peak_success_rate >= 0.8 else 'PARTIAL' if peak_success_rate >= 0.5 else 'FAILED'}")

    # Test 2: Connectivity transition at K=N-2
    connectivity_transitions = []
    for N in sorted(connectivity_df['N'].unique()):
        data_n = connectivity_df[connectivity_df['N'] == N].sort_values('K')

        # Find first K where graph is connected
        connected_data = data_n[data_n['is_connected'] == True]
        if not connected_data.empty:
            first_connected_k = connected_data['K'].iloc[0]
            predicted_k = N - 2

            connectivity_transitions.append({
                'N': N,
                'first_connected_K': first_connected_k,
                'predicted_K': predicted_k,
                'matches': first_connected_k == predicted_k,
                'close': abs(first_connected_k - predicted_k) <= 1
            })

    if connectivity_transitions:
        trans_df = pd.DataFrame(connectivity_transitions)
        exact_matches = trans_df['matches'].sum()
        close_matches = trans_df['close'].sum()
        total = len(trans_df)

        print(f"\nTest 2: Connectivity Transition Point")
        print(f"  Hypothesis: Graph becomes connected at K=N-2")
        print(f"  Exact matches: {exact_matches}/{total} ({exact_matches/total:.1%})")
        print(f"  Within ±1: {close_matches}/{total} ({close_matches/total:.1%})")
        print(f"  Status: {'VALIDATED' if exact_matches/total >= 0.7 else 'PARTIAL' if close_matches/total >= 0.7 else 'FAILED'}")

    # Test 3: K=N-2 pattern consistency
    print(f"\nTest 3: Pattern Consistency K(N) = N-2")
    print(f"  Verified cases:")
    for _, row in peak_df.iterrows():
        N = int(row['N'])
        k_peak = int(row['K_at_peak'])
        k_pred = int(row['K_predicted'])
        status = "OK" if k_peak == k_pred else f"MISMATCH (peak at K={k_peak})"
        print(f"    N={N}: K={k_pred} {status}")

    # Overall assessment
    print(f"\n" + "="*80)
    print("OVERALL ASSESSMENT")
    print("="*80)

    if peak_success_rate >= 0.8:
        print("GEOMETRIC HYPOTHESIS: STRONGLY SUPPORTED")
        print("  - Entropy density consistently peaks at K=N-2")
        print("  - K(N)=N-2 appears to be geometrically fundamental")
        print("  - Pattern likely reflects permutohedron structure")
    elif peak_success_rate >= 0.5:
        print("GEOMETRIC HYPOTHESIS: PARTIALLY SUPPORTED")
        print("  - Entropy density shows preference for K near N-2")
        print("  - Some deviations suggest refinements needed")
    else:
        print("GEOMETRIC HYPOTHESIS: NOT SUPPORTED")
        print("  - Entropy density does not peak at K=N-2")
        print("  - Alternative derivation approach needed")

    return {
        'peak_success_rate': peak_success_rate,
        'n_matches': n_matches,
        'n_total': n_values,
        'connectivity_transitions': connectivity_transitions if connectivity_transitions else None
    }

def main():
    """Main execution"""

    print("\n" + "#"*80)
    print("# ENTROPY DENSITY & CONNECTIVITY ANALYSIS")
    print("# Validating K(N) = N-2 Geometric Hypothesis")
    print("#"*80 + "\n")

    # Analysis parameters
    N_MAX_ENTROPY = 8  # Up to N=8 for entropy analysis
    N_MAX_CONNECTIVITY = 6  # Up to N=6 for connectivity (computationally intensive)

    # Run analyses
    entropy_df = entropy_density_analysis(N_MAX_ENTROPY)
    connectivity_df = connectivity_analysis(N_MAX_CONNECTIVITY)

    # Visualize
    peak_df = visualize_results(entropy_df, connectivity_df)

    # Validate hypothesis
    validation_results = validate_hypothesis(entropy_df, connectivity_df, peak_df)

    # Save results
    output_dir = './outputs'
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    entropy_df.to_csv(f'{output_dir}/entropy_density_data_{timestamp}.csv', index=False)
    connectivity_df.to_csv(f'{output_dir}/connectivity_data_{timestamp}.csv', index=False)

    summary = {
        'timestamp': timestamp,
        'analysis_parameters': {
            'N_max_entropy': N_MAX_ENTROPY,
            'N_max_connectivity': N_MAX_CONNECTIVITY
        },
        'validation_results': validation_results,
        'peak_locations': peak_df.to_dict('records')
    }

    with open(f'{output_dir}/validation_summary_{timestamp}.json', 'w') as f:
        json.dump(summary, f, indent=2, default=str)

    print(f"\nResults saved:")
    print(f"  - Entropy data: entropy_density_data_{timestamp}.csv")
    print(f"  - Connectivity data: connectivity_data_{timestamp}.csv")
    print(f"  - Summary: validation_summary_{timestamp}.json")

    print("\n" + "#"*80)
    print("# ANALYSIS COMPLETE")
    print("#"*80 + "\n")

if __name__ == "__main__":
    main()
