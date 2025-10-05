"""
Diameter Relationship Test: K(N) = N-2 Hypothesis

CRITICAL FINDING from entropy density data:
At K=N-2, graph diameter d = 2K for all N tested (N=3..6)

HYPOTHESIS: This relationship (d=2K) uniquely characterizes K=N-2

This script tests whether d=2K holds:
1. ONLY at K=N-2 (strong geometric principle)
2. For all K values (coincidence, not explanatory)
3. For some other pattern

If (1) is true, we have found the geometric principle deriving K(N)=N-2!
"""

import itertools
import networkx as nx
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
from collections import defaultdict
import math

def inversion_count(perm):
    """Count inversions in permutation"""
    count = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                count += 1
    return count

def build_constraint_graph(N, K):
    """
    Build graph of valid permutations (h(sigma) <= K)
    connected by adjacent transpositions
    """
    G = nx.Graph()

    # Generate all permutations and filter by inversion count
    all_perms = list(itertools.permutations(range(N)))
    valid_perms = [p for p in all_perms if inversion_count(p) <= K]

    # Add all valid permutations as nodes
    for perm in valid_perms:
        G.add_node(perm)

    # Add edges for adjacent transpositions
    for perm in valid_perms:
        perm_list = list(perm)
        # Try all adjacent transpositions
        for i in range(N-1):
            # Swap positions i and i+1
            neighbor = perm_list.copy()
            neighbor[i], neighbor[i+1] = neighbor[i+1], neighbor[i]
            neighbor_tuple = tuple(neighbor)

            # Add edge if neighbor is also valid
            if neighbor_tuple in valid_perms:
                G.add_edge(perm, neighbor_tuple)

    return G

def analyze_diameter_relationship(N_max=6):
    """
    Test diameter relationship d vs K for all N

    Returns:
        DataFrame with columns: N, K, V, E, diameter, d/K, d/(N-1), is_K_N_minus_2, d_equals_2K
    """
    results = []

    print(f"Testing diameter relationship for N=3 to {N_max}...")
    print("=" * 80)

    for N in range(3, N_max + 1):
        max_inversions = N * (N - 1) // 2
        K_target = N - 2

        print(f"\nN={N} (max inversions = {max_inversions}, K(N)=N-2 = {K_target})")
        print("-" * 60)

        for K in range(0, min(max_inversions + 1, 20)):  # Limit K for tractability
            # Build graph
            G = build_constraint_graph(N, K)

            # Compute metrics
            V = G.number_of_nodes()
            E = G.number_of_edges()

            if V == 0:
                continue

            # Diameter (handle disconnected case)
            if nx.is_connected(G):
                diameter = nx.diameter(G)
            else:
                # Use diameter of largest component
                largest_cc = max(nx.connected_components(G), key=len)
                diameter = nx.diameter(G.subgraph(largest_cc))

            # Compute ratios
            d_over_K = diameter / K if K > 0 else float('inf')
            d_over_N_minus_1 = diameter / (N - 1)

            # Check conditions
            is_K_N_minus_2 = (K == K_target)
            d_equals_2K = abs(d_over_K - 2.0) < 0.01 if K > 0 else False

            results.append({
                'N': N,
                'K': K,
                'V': V,
                'E': E,
                'diameter': diameter,
                'd/K': d_over_K,
                'd/(N-1)': d_over_N_minus_1,
                'is_K_N_minus_2': is_K_N_minus_2,
                'd_equals_2K': d_equals_2K
            })

            # Print key results
            marker = " <-- K=N-2" if is_K_N_minus_2 else ""
            check = " [d=2K!]" if d_equals_2K else ""
            print(f"  K={K:2d}: V={V:4d}, E={E:5d}, d={diameter:3d}, d/K={d_over_K:5.2f}{check}{marker}")

    df = pd.DataFrame(results)
    return df

def visualize_diameter_relationship(df):
    """Create comprehensive visualization of diameter relationships"""

    fig, axes = plt.subplots(2, 3, figsize=(18, 12))
    fig.suptitle('Diameter Relationship Analysis: Testing d=2K at K=N-2',
                 fontsize=16, fontweight='bold')

    # Color scheme
    colors = plt.cm.tab10(np.linspace(0, 1, 10))
    N_values = sorted(df['N'].unique())

    # Plot 1: d/K vs K (key test!)
    ax = axes[0, 0]
    for i, N in enumerate(N_values):
        N_data = df[(df['N'] == N) & (df['K'] > 0)]
        K_target = N - 2

        # Plot all points
        ax.plot(N_data['K'], N_data['d/K'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        # Highlight K=N-2 point
        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax.plot(target_point['K'], target_point['d/K'], '*',
                   color=colors[i], markersize=20, markeredgecolor='red',
                   markeredgewidth=2)

    ax.axhline(y=2.0, color='red', linestyle='--', linewidth=2,
               label='d/K = 2.0', alpha=0.7)
    ax.set_xlabel('Constraint Threshold K', fontsize=12)
    ax.set_ylabel('Diameter / K', fontsize=12)
    ax.set_title('Critical Test: Does d=2K hold only at K=N-2?', fontsize=13, fontweight='bold')
    ax.legend(fontsize=9, loc='best')
    ax.grid(True, alpha=0.3)

    # Plot 2: Diameter vs K
    ax = axes[0, 1]
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax.plot(N_data['K'], N_data['diameter'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        # Highlight K=N-2
        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax.plot(target_point['K'], target_point['diameter'], '*',
                   color=colors[i], markersize=20, markeredgecolor='red',
                   markeredgewidth=2)

    ax.set_xlabel('Constraint Threshold K', fontsize=12)
    ax.set_ylabel('Graph Diameter d', fontsize=12)
    ax.set_title('Diameter vs K (stars show K=N-2)', fontsize=13)
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    # Plot 3: d=2K validation table
    ax = axes[0, 2]
    ax.axis('off')

    validation_text = "d=2K Validation at K=N-2\n" + "="*40 + "\n\n"
    validation_text += f"{'N':<4} {'K':<4} {'d':<5} {'d/K':<7} {'d=2K?':<8}\n"
    validation_text += "-"*40 + "\n"

    for N in N_values:
        K_target = N - 2
        row = df[(df['N'] == N) & (df['K'] == K_target)]
        if not row.empty:
            d = int(row['diameter'].values[0])
            d_over_K = row['d/K'].values[0]
            check = "YES" if row['d_equals_2K'].values[0] else "NO"
            validation_text += f"{N:<4} {K_target:<4} {d:<5} {d_over_K:<7.2f} {check:<8}\n"

    ax.text(0.1, 0.9, validation_text, transform=ax.transAxes,
           fontsize=11, verticalalignment='top', fontfamily='monospace',
           bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))

    # Plot 4: Uniqueness test - count d=2K occurrences per N
    ax = axes[1, 0]
    uniqueness_data = []
    for N in N_values:
        N_data = df[df['N'] == N]
        total_K = len(N_data)
        d_equals_2K_count = N_data['d_equals_2K'].sum()
        K_target = N - 2

        # Check if K=N-2 is the ONLY K where d=2K
        unique = (d_equals_2K_count == 1) and N_data[N_data['K'] == K_target]['d_equals_2K'].values[0]

        uniqueness_data.append({
            'N': N,
            'total_K': total_K,
            'd=2K_count': d_equals_2K_count,
            'unique_to_K_N_minus_2': unique
        })

    uniqueness_df = pd.DataFrame(uniqueness_data)

    x_pos = np.arange(len(N_values))
    ax.bar(x_pos, uniqueness_df['d=2K_count'], alpha=0.7, color='steelblue',
           edgecolor='black', linewidth=1.5)
    ax.axhline(y=1, color='red', linestyle='--', linewidth=2,
               label='Unique (count=1)', alpha=0.7)
    ax.set_xticks(x_pos)
    ax.set_xticklabels([f'N={N}' for N in N_values])
    ax.set_ylabel('Number of K values with d=2K', fontsize=12)
    ax.set_title('Uniqueness Test: Is d=2K exclusive to K=N-2?', fontsize=13, fontweight='bold')
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3, axis='y')

    # Plot 5: d/(N-1) vs K
    ax = axes[1, 1]
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax.plot(N_data['K'], N_data['d/(N-1)'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax.plot(target_point['K'], target_point['d/(N-1)'], '*',
                   color=colors[i], markersize=20, markeredgecolor='red',
                   markeredgewidth=2)

    ax.set_xlabel('Constraint Threshold K', fontsize=12)
    ax.set_ylabel('Diameter / (N-1)', fontsize=12)
    ax.set_title('Diameter normalized by permutohedron dimension', fontsize=13)
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    # Plot 6: Summary statistics
    ax = axes[1, 2]
    ax.axis('off')

    summary_text = "HYPOTHESIS TEST SUMMARY\n" + "="*40 + "\n\n"
    summary_text += "Question: Does d=2K hold ONLY at K=N-2?\n\n"

    all_unique = all(uniqueness_df['unique_to_K_N_minus_2'])

    if all_unique:
        summary_text += "RESULT: YES - HYPOTHESIS CONFIRMED!\n\n"
        summary_text += "For all tested N, the relationship\n"
        summary_text += "d=2K holds EXCLUSIVELY at K=N-2.\n\n"
        summary_text += "CONCLUSION:\n"
        summary_text += "K(N)=N-2 is the unique constraint\n"
        summary_text += "threshold ensuring graph diameter\n"
        summary_text += "equals twice the threshold.\n\n"
        summary_text += "GEOMETRIC PRINCIPLE FOUND!\n"
        color = 'lightgreen'
    else:
        summary_text += "RESULT: PARTIAL/NO\n\n"
        for idx, row in uniqueness_df.iterrows():
            if not row['unique_to_K_N_minus_2']:
                summary_text += f"N={row['N']}: d=2K occurs at "
                summary_text += f"{int(row['d=2K_count'])} values of K\n"

        summary_text += "\nCONCLUSION:\n"
        summary_text += "d=2K relationship not unique to\n"
        summary_text += "K=N-2. Alternative explanation needed.\n"
        color = 'lightcoral'

    ax.text(0.1, 0.9, summary_text, transform=ax.transAxes,
           fontsize=11, verticalalignment='top', fontfamily='monospace',
           bbox=dict(boxstyle='round', facecolor=color, alpha=0.5))

    plt.tight_layout()
    return fig

def main():
    """Run comprehensive diameter relationship analysis"""

    print("\n" + "="*80)
    print("DIAMETER RELATIONSHIP TEST: K(N) = N-2 HYPOTHESIS")
    print("="*80)
    print("\nCRITICAL QUESTION: Does d=2K hold ONLY at K=N-2?\n")

    # Run analysis
    df = analyze_diameter_relationship(N_max=6)

    # Save raw data
    import os
    output_dir = 'outputs' if os.path.exists('outputs') else os.path.join(os.path.dirname(__file__), 'outputs')
    os.makedirs(output_dir, exist_ok=True)

    output_file = os.path.join(output_dir, 'diameter_relationship_data.csv')
    df.to_csv(output_file, index=False)
    print(f"\nData saved to: {output_file}")

    # Create visualization
    print("\nGenerating visualization...")
    fig = visualize_diameter_relationship(df)

    plot_file = os.path.join(output_dir, 'diameter_relationship_analysis.png')
    fig.savefig(plot_file, dpi=150, bbox_inches='tight')
    print(f"Plot saved to: {plot_file}")

    # Final statistical summary
    print("\n" + "="*80)
    print("FINAL VERDICT")
    print("="*80)

    N_values = sorted(df['N'].unique())
    for N in N_values:
        K_target = N - 2
        N_data = df[df['N'] == N]

        d_2K_rows = N_data[N_data['d_equals_2K'] == True]
        count = len(d_2K_rows)

        # Check if ONLY K=N-2 satisfies d=2K
        if count == 1 and d_2K_rows['K'].values[0] == K_target:
            verdict = "UNIQUE - d=2K holds ONLY at K=N-2"
            symbol = "✓"
        elif count == 0:
            verdict = "NEVER - d=2K does not hold"
            symbol = "✗"
        else:
            K_list = d_2K_rows['K'].tolist()
            verdict = f"NOT UNIQUE - d=2K at K={K_list}"
            symbol = "~"

        print(f"\nN={N}: {symbol} {verdict}")

    print("\n" + "="*80)
    print("Analysis complete!")
    print("="*80)

if __name__ == "__main__":
    main()
