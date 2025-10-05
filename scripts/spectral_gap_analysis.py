"""
Spectral Gap Analysis: K(N) = N-2 Hypothesis

CRITICAL TEST: Does the spectral gap (algebraic connectivity) of the
constraint graph optimize at K=N-2?

Spectral gap λ₂ - λ₁ measures:
- Mixing time for random walks (relevant to L-flow)
- Quality of connectivity (not just existence)
- Graph expansion properties
- Synchronization and consensus dynamics

CONNECTION TO LFT:
- L-flow is descent on permutohedron
- Random walk mixing time relates to time emergence
- Spectral gap determines convergence rate to equilibrium

HYPOTHESIS: K=N-2 optimizes spectral properties, enabling stable L-flow dynamics
"""

import itertools
import networkx as nx
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
from scipy import linalg
import os

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

    if len(valid_perms) == 0:
        return G

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

def compute_spectral_properties(G):
    """
    Compute comprehensive spectral properties of graph

    Returns dict with:
    - eigenvalues: all Laplacian eigenvalues (sorted)
    - spectral_gap: λ₂ - λ₁ (algebraic connectivity)
    - fiedler: λ₂ (Fiedler eigenvalue)
    - spectral_radius: max eigenvalue
    - normalized_gap: gap / max eigenvalue
    """
    if G.number_of_nodes() == 0:
        return None

    if G.number_of_nodes() == 1:
        return {
            'eigenvalues': np.array([0.0]),
            'spectral_gap': 0.0,
            'fiedler': 0.0,
            'spectral_radius': 0.0,
            'normalized_gap': 0.0,
            'avg_eigenvalue': 0.0
        }

    # Compute Laplacian matrix
    L = nx.laplacian_matrix(G).toarray()

    # Compute eigenvalues (sorted ascending)
    eigenvalues = linalg.eigvalsh(L)
    eigenvalues.sort()

    # Spectral gap (algebraic connectivity)
    spectral_gap = eigenvalues[1] - eigenvalues[0]

    # Fiedler eigenvalue (second smallest, should equal eigenvalues[1])
    fiedler = eigenvalues[1]

    # Spectral radius (largest eigenvalue)
    spectral_radius = eigenvalues[-1]

    # Normalized spectral gap
    normalized_gap = spectral_gap / spectral_radius if spectral_radius > 0 else 0.0

    # Average eigenvalue (excluding λ₁=0)
    avg_eigenvalue = np.mean(eigenvalues[1:]) if len(eigenvalues) > 1 else 0.0

    return {
        'eigenvalues': eigenvalues,
        'spectral_gap': spectral_gap,
        'fiedler': fiedler,
        'spectral_radius': spectral_radius,
        'normalized_gap': normalized_gap,
        'avg_eigenvalue': avg_eigenvalue
    }

def spectral_gap_analysis(N_max=6):
    """
    Test spectral gap hypothesis: does any spectral metric optimize at K=N-2?

    Tests:
    1. Spectral gap λ₂ - λ₁
    2. Fiedler eigenvalue λ₂
    3. Normalized gap (λ₂ - λ₁) / λ_max
    4. Average eigenvalue
    5. Gap-to-size ratio
    """
    results = []

    print(f"Spectral Gap Analysis for N=3 to {N_max}")
    print("=" * 80)

    for N in range(3, N_max + 1):
        max_inversions = N * (N - 1) // 2
        K_target = N - 2

        print(f"\nN={N} (K(N)=N-2 = {K_target})")
        print("-" * 60)

        for K in range(0, min(max_inversions + 1, 20)):
            # Build graph
            G = build_constraint_graph(N, K)

            V = G.number_of_nodes()
            E = G.number_of_edges()

            if V == 0:
                continue

            # Compute spectral properties
            spectral = compute_spectral_properties(G)

            if spectral is None:
                continue

            # Additional metrics
            gap_to_size = spectral['spectral_gap'] / V if V > 0 else 0.0
            gap_to_edges = spectral['spectral_gap'] / E if E > 0 else 0.0

            is_K_N_minus_2 = (K == K_target)

            results.append({
                'N': N,
                'K': K,
                'V': V,
                'E': E,
                'spectral_gap': spectral['spectral_gap'],
                'fiedler': spectral['fiedler'],
                'spectral_radius': spectral['spectral_radius'],
                'normalized_gap': spectral['normalized_gap'],
                'avg_eigenvalue': spectral['avg_eigenvalue'],
                'gap_to_size': gap_to_size,
                'gap_to_edges': gap_to_edges,
                'is_K_N_minus_2': is_K_N_minus_2
            })

            # Print key results
            marker = " <-- K=N-2" if is_K_N_minus_2 else ""
            print(f"  K={K:2d}: V={V:4d}, gap={spectral['spectral_gap']:6.3f}, "
                  f"norm_gap={spectral['normalized_gap']:5.3f}{marker}")

    df = pd.DataFrame(results)
    return df

def test_optimization_hypotheses(df):
    """
    Test if any spectral metric is optimized at K=N-2

    Returns validation results for each hypothesis
    """
    print("\n" + "=" * 80)
    print("OPTIMIZATION HYPOTHESIS TESTS")
    print("=" * 80)

    metrics = [
        ('spectral_gap', 'Spectral gap lambda2-lambda1'),
        ('fiedler', 'Fiedler eigenvalue lambda2'),
        ('normalized_gap', 'Normalized gap (lambda2-lambda1)/lambda_max'),
        ('avg_eigenvalue', 'Average eigenvalue'),
        ('gap_to_size', 'Gap / vertex count'),
        ('gap_to_edges', 'Gap / edge count')
    ]

    results = {}

    for metric_name, metric_label in metrics:
        print(f"\n{metric_label}:")
        print("-" * 50)

        matches = 0
        total = 0

        for N in sorted(df['N'].unique()):
            N_data = df[df['N'] == N].copy()
            K_target = N - 2

            # Find K that maximizes this metric
            max_idx = N_data[metric_name].idxmax()
            K_at_max = N_data.loc[max_idx, 'K']
            max_value = N_data.loc[max_idx, metric_name]

            # Get value at K=N-2
            target_row = N_data[N_data['K'] == K_target]
            if not target_row.empty:
                target_value = target_row[metric_name].values[0]
            else:
                target_value = np.nan

            match = (K_at_max == K_target)
            matches += int(match)
            total += 1

            status = "YES" if match else "NO"
            print(f"  N={N}: max at K={K_at_max:.0f} (value={max_value:.3f}), "
                  f"K=N-2 at K={K_target} (value={target_value:.3f}) {status}")

        success_rate = matches / total if total > 0 else 0.0
        results[metric_name] = {
            'matches': matches,
            'total': total,
            'success_rate': success_rate,
            'label': metric_label
        }

        print(f"\nSuccess rate: {matches}/{total} ({success_rate:.1%})")

    return results

def visualize_spectral_analysis(df, validation_results):
    """Create comprehensive spectral gap visualization"""

    fig = plt.figure(figsize=(18, 12))
    gs = fig.add_gridspec(3, 3, hspace=0.3, wspace=0.3)

    colors = plt.cm.tab10(np.linspace(0, 1, 10))
    N_values = sorted(df['N'].unique())

    # Plot 1: Spectral gap vs K
    ax1 = fig.add_subplot(gs[0, 0])
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax1.plot(N_data['K'], N_data['spectral_gap'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        # Highlight K=N-2
        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax1.plot(target_point['K'], target_point['spectral_gap'], '*',
                    color=colors[i], markersize=20, markeredgecolor='red',
                    markeredgewidth=2)

    ax1.set_xlabel('Constraint Threshold K', fontsize=11)
    ax1.set_ylabel('Spectral Gap', fontsize=11)
    ax1.set_title('Spectral Gap vs K\n(stars show K=N-2)', fontsize=12, fontweight='bold')
    ax1.legend(fontsize=9)
    ax1.grid(True, alpha=0.3)

    # Plot 2: Fiedler eigenvalue
    ax2 = fig.add_subplot(gs[0, 1])
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax2.plot(N_data['K'], N_data['fiedler'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax2.plot(target_point['K'], target_point['fiedler'], '*',
                    color=colors[i], markersize=20, markeredgecolor='red',
                    markeredgewidth=2)

    ax2.set_xlabel('Constraint Threshold K', fontsize=11)
    ax2.set_ylabel('Fiedler Eigenvalue', fontsize=11)
    ax2.set_title('Algebraic Connectivity', fontsize=12, fontweight='bold')
    ax2.legend(fontsize=9)
    ax2.grid(True, alpha=0.3)

    # Plot 3: Normalized gap
    ax3 = fig.add_subplot(gs[0, 2])
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax3.plot(N_data['K'], N_data['normalized_gap'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax3.plot(target_point['K'], target_point['normalized_gap'], '*',
                    color=colors[i], markersize=20, markeredgecolor='red',
                    markeredgewidth=2)

    ax3.set_xlabel('Constraint Threshold K', fontsize=11)
    ax3.set_ylabel('Normalized Gap', fontsize=11)
    ax3.set_title('Normalized Spectral Gap', fontsize=12, fontweight='bold')
    ax3.legend(fontsize=9)
    ax3.grid(True, alpha=0.3)

    # Plot 4: Success rates bar chart
    ax4 = fig.add_subplot(gs[1, 0])
    metric_names = list(validation_results.keys())
    success_rates = [validation_results[m]['success_rate'] for m in metric_names]
    labels = [validation_results[m]['label'].split()[0] for m in metric_names]

    bars = ax4.barh(labels, success_rates, color='steelblue', alpha=0.7,
                    edgecolor='black', linewidth=1.5)
    ax4.axvline(x=1.0, color='green', linestyle='--', linewidth=2,
                label='100% success', alpha=0.7)
    ax4.set_xlabel('Success Rate', fontsize=11)
    ax4.set_title('Optimization Test Results', fontsize=12, fontweight='bold')
    ax4.set_xlim(0, 1.1)
    ax4.legend(fontsize=9)
    ax4.grid(True, alpha=0.3, axis='x')

    # Color bars by success
    for bar, rate in zip(bars, success_rates):
        if rate == 1.0:
            bar.set_color('green')
        elif rate >= 0.5:
            bar.set_color('orange')
        else:
            bar.set_color('red')

    # Plot 5: Gap-to-size ratio
    ax5 = fig.add_subplot(gs[1, 1])
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax5.plot(N_data['K'], N_data['gap_to_size'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax5.plot(target_point['K'], target_point['gap_to_size'], '*',
                    color=colors[i], markersize=20, markeredgecolor='red',
                    markeredgewidth=2)

    ax5.set_xlabel('Constraint Threshold K', fontsize=11)
    ax5.set_ylabel('Gap / Vertex Count', fontsize=11)
    ax5.set_title('Spectral Gap Efficiency', fontsize=12, fontweight='bold')
    ax5.legend(fontsize=9)
    ax5.grid(True, alpha=0.3)

    # Plot 6: Eigenvalue spectrum at K=N-2
    ax6 = fig.add_subplot(gs[1, 2])
    for N in [3, 4, 5]:
        K_target = N - 2
        G = build_constraint_graph(N, K_target)
        spectral = compute_spectral_properties(G)

        if spectral is not None:
            eigenvalues = spectral['eigenvalues']
            ax6.plot(range(len(eigenvalues)), eigenvalues, 'o-',
                    label=f'N={N}, K={K_target}', markersize=5, alpha=0.7)

    ax6.set_xlabel('Eigenvalue Index', fontsize=11)
    ax6.set_ylabel('Eigenvalue', fontsize=11)
    ax6.set_title('Laplacian Spectrum at K=N-2', fontsize=12, fontweight='bold')
    ax6.legend(fontsize=9)
    ax6.grid(True, alpha=0.3)

    # Plot 7-9: Detailed analysis for N=4,5,6
    for idx, N in enumerate([4, 5, 6]):
        ax = fig.add_subplot(gs[2, idx])
        N_data = df[df['N'] == N]
        K_target = N - 2

        # Plot multiple metrics
        ax_twin1 = ax.twinx()

        l1 = ax.plot(N_data['K'], N_data['spectral_gap'], 'b-o',
                    label='Spectral gap', markersize=6, linewidth=2)
        l2 = ax_twin1.plot(N_data['K'], N_data['normalized_gap'], 'r-s',
                          label='Normalized gap', markersize=5, linewidth=2, alpha=0.7)

        # Highlight K=N-2
        ax.axvline(x=K_target, color='green', linestyle='--', linewidth=2,
                  alpha=0.5, label=f'K=N-2={K_target}')

        ax.set_xlabel('K', fontsize=10)
        ax.set_ylabel('Spectral Gap', fontsize=10, color='b')
        ax_twin1.set_ylabel('Normalized Gap', fontsize=10, color='r')
        ax.set_title(f'N={N} Detailed Analysis', fontsize=11, fontweight='bold')
        ax.tick_params(axis='y', labelcolor='b')
        ax_twin1.tick_params(axis='y', labelcolor='r')
        ax.grid(True, alpha=0.3)

        # Combined legend
        lines = l1 + l2
        labels = [l.get_label() for l in lines]
        ax.legend(lines, labels, fontsize=8, loc='upper left')

    fig.suptitle('Spectral Gap Analysis: Testing K(N)=N-2 Hypothesis',
                fontsize=16, fontweight='bold', y=0.995)

    return fig

def final_verdict(validation_results):
    """Determine final verdict on spectral gap hypothesis"""

    print("\n" + "=" * 80)
    print("FINAL VERDICT: SPECTRAL GAP HYPOTHESIS")
    print("=" * 80)

    # Check if any metric has 100% success
    perfect_metrics = [m for m, r in validation_results.items()
                      if r['success_rate'] == 1.0]

    # Check if any metric has >50% success
    strong_metrics = [m for m, r in validation_results.items()
                     if r['success_rate'] >= 0.5]

    if perfect_metrics:
        print(f"\nHYPOTHESIS CONFIRMED!")
        print(f"\nMetrics with 100% success:")
        for m in perfect_metrics:
            print(f"  - {validation_results[m]['label']}")
        print(f"\nK(N)=N-2 UNIQUELY OPTIMIZES: {validation_results[perfect_metrics[0]]['label']}")
        print(f"\n** GEOMETRIC PRINCIPLE FOUND **")
        return "CONFIRMED"

    elif strong_metrics:
        print(f"\nHYPOTHESIS PARTIALLY SUPPORTED")
        print(f"\nMetrics with >=50% success:")
        for m in strong_metrics:
            rate = validation_results[m]['success_rate']
            print(f"  - {validation_results[m]['label']}: {rate:.1%}")
        print(f"\nK=N-2 shows SOME spectral optimization but not universal")
        return "PARTIAL"

    else:
        print(f"\nHYPOTHESIS REFUTED")
        print(f"\nNo spectral metric consistently optimized at K=N-2")
        best_metric = max(validation_results.items(),
                         key=lambda x: x[1]['success_rate'])
        print(f"Best metric: {best_metric[1]['label']} "
              f"({best_metric[1]['success_rate']:.1%} success)")
        return "REFUTED"

def main():
    """Run comprehensive spectral gap analysis"""

    print("\n" + "=" * 80)
    print("SPECTRAL GAP ANALYSIS: K(N) = N-2 HYPOTHESIS")
    print("=" * 80)
    print("\nCRITICAL QUESTION: Does spectral gap optimize at K=N-2?")
    print("\nConnection to LFT:")
    print("  - Spectral gap determines random walk mixing time")
    print("  - L-flow dynamics may require optimal mixing")
    print("  - Time emergence connected to graph spectral properties")
    print()

    # Run analysis
    df = spectral_gap_analysis(N_max=6)

    # Save raw data
    output_dir = 'outputs' if os.path.exists('outputs') else os.path.join(os.path.dirname(__file__), 'outputs')
    os.makedirs(output_dir, exist_ok=True)

    output_file = os.path.join(output_dir, 'spectral_gap_data.csv')
    df.to_csv(output_file, index=False)
    print(f"\nData saved to: {output_file}")

    # Test optimization hypotheses
    validation_results = test_optimization_hypotheses(df)

    # Create visualization
    print("\nGenerating visualization...")
    fig = visualize_spectral_analysis(df, validation_results)

    plot_file = os.path.join(output_dir, 'spectral_gap_analysis.png')
    fig.savefig(plot_file, dpi=150, bbox_inches='tight')
    print(f"Plot saved to: {plot_file}")
    plt.show()

    # Final verdict
    verdict = final_verdict(validation_results)

    # Save summary
    summary = {
        'verdict': verdict,
        'metrics_tested': len(validation_results),
        'perfect_matches': sum(1 for r in validation_results.values() if r['success_rate'] == 1.0),
        'strong_matches': sum(1 for r in validation_results.values() if r['success_rate'] >= 0.5),
        'validation_results': {k: {'success_rate': v['success_rate'],
                                   'matches': v['matches'],
                                   'total': v['total']}
                              for k, v in validation_results.items()}
    }

    import json
    summary_file = os.path.join(output_dir, 'spectral_gap_summary.json')
    with open(summary_file, 'w') as f:
        json.dump(summary, f, indent=2)

    print(f"\nSummary saved to: {summary_file}")
    print("\n" + "=" * 80)
    print("Analysis complete!")
    print("=" * 80)

if __name__ == "__main__":
    main()
