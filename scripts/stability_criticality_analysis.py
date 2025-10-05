"""
Stability/Criticality Analysis: K(N) = N-2 Hypothesis

REFRAMED QUESTION: Is K=N-2 a critical point or stability boundary?

Previous tests (optimization hypotheses) all failed:
- Entropy density ❌
- Diameter uniqueness ❌
- Spectral gap ❌

NEW FRAMEWORK: K=N-2 as phase transition / stability threshold

TESTS:
1. L-flow convergence rate - does it change sharply at K=N-2?
2. Constraint saturation - does K=N-2 mark stability boundary?
3. Completion uniqueness - phase transition in determinism?
4. Effective temperature - thermodynamic critical point?
5. Order parameter - does system behavior bifurcate?

CONNECTION TO NOTEBOOK 05:
- N=4 is maximum stable complexity
- L-flow success rate drops beyond N=4
- This suggests STABILITY, not optimization
"""

import itertools
import networkx as nx
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
import os
from collections import defaultdict

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
    """Build graph of valid permutations"""
    G = nx.Graph()
    all_perms = list(itertools.permutations(range(N)))
    valid_perms = [p for p in all_perms if inversion_count(p) <= K]

    if len(valid_perms) == 0:
        return G, []

    for perm in valid_perms:
        G.add_node(perm)

    for perm in valid_perms:
        perm_list = list(perm)
        for i in range(N-1):
            neighbor = perm_list.copy()
            neighbor[i], neighbor[i+1] = neighbor[i+1], neighbor[i]
            neighbor_tuple = tuple(neighbor)
            if neighbor_tuple in valid_perms:
                G.add_edge(perm, neighbor_tuple)

    return G, valid_perms

def lflow_simulation(N, K, trials=500, max_steps=100, seed=42):
    """
    Simulate L-flow dynamics: start from random valid permutation,
    descend via h(sigma) until reaching minimum

    Returns:
    - convergence_rate: average steps to reach minimum
    - success_rate: fraction reaching unique minimum
    - trajectory_variance: spread in paths taken
    """
    rng = np.random.default_rng(seed)
    G, valid_perms = build_constraint_graph(N, K)

    if len(valid_perms) == 0:
        return None

    # Find minimum inversion permutations
    h_values = {p: inversion_count(p) for p in valid_perms}
    min_h = min(h_values.values())
    minima = [p for p in valid_perms if h_values[p] == min_h]

    convergence_steps = []
    successes = 0
    trajectory_lengths = []

    for trial in range(trials):
        # Start from random valid permutation
        current = valid_perms[rng.integers(0, len(valid_perms))]
        path = [current]

        for step in range(max_steps):
            # Check if at minimum
            if h_values[current] == min_h:
                convergence_steps.append(step)
                successes += 1
                trajectory_lengths.append(len(path))
                break

            # Find neighbors with lower h
            neighbors = list(G.neighbors(current))
            if not neighbors:
                break

            # Greedy descent: pick neighbor with lowest h
            h_neighbors = [(n, h_values[n]) for n in neighbors]
            h_neighbors.sort(key=lambda x: x[1])

            # If no lower neighbor, stuck
            if h_neighbors[0][1] >= h_values[current]:
                trajectory_lengths.append(len(path))
                break

            # Move to lowest neighbor (deterministic greedy)
            current = h_neighbors[0][0]
            path.append(current)
        else:
            # Max steps reached without convergence
            trajectory_lengths.append(len(path))

    if len(convergence_steps) == 0:
        avg_convergence = max_steps
    else:
        avg_convergence = np.mean(convergence_steps)

    success_rate = successes / trials
    trajectory_var = np.var(trajectory_lengths) if trajectory_lengths else 0.0

    return {
        'avg_convergence': avg_convergence,
        'success_rate': success_rate,
        'trajectory_variance': trajectory_var,
        'num_minima': len(minima),
        'trials_converged': successes
    }

def constraint_saturation_analysis(N, K):
    """
    Analyze how "saturated" the constraint space is

    Measures:
    - Constraint density: K / K_max
    - State space reduction: |V_K| / N!
    - Effective degrees of freedom
    """
    G, valid_perms = build_constraint_graph(N, K)

    K_max = N * (N - 1) // 2
    factorial_N = np.math.factorial(N)

    constraint_density = K / K_max if K_max > 0 else 0
    state_reduction = len(valid_perms) / factorial_N if factorial_N > 0 else 0

    # Effective degrees of freedom: log|V_K|
    if len(valid_perms) > 0:
        eff_dof = np.log(len(valid_perms))
    else:
        eff_dof = 0

    return {
        'constraint_density': constraint_density,
        'state_reduction': state_reduction,
        'effective_dof': eff_dof,
        'V_K': len(valid_perms)
    }

def completion_uniqueness_test(N, K, samples=200, seed=42):
    """
    Test if constraint set K uniquely determines final state

    Start from multiple initial conditions, measure:
    - Fraction reaching same final state
    - Number of distinct attractors
    - Basin sizes
    """
    rng = np.random.default_rng(seed)
    G, valid_perms = build_constraint_graph(N, K)

    if len(valid_perms) == 0:
        return None

    h_values = {p: inversion_count(p) for p in valid_perms}
    min_h = min(h_values.values())

    final_states = defaultdict(int)

    for sample in range(samples):
        current = valid_perms[rng.integers(0, len(valid_perms))]

        # Greedy descent
        for _ in range(100):
            if h_values[current] == min_h:
                break

            neighbors = list(G.neighbors(current))
            if not neighbors:
                break

            h_neighbors = [(n, h_values[n]) for n in neighbors]
            h_neighbors.sort(key=lambda x: x[1])

            if h_neighbors[0][1] >= h_values[current]:
                break

            current = h_neighbors[0][0]

        final_states[current] += 1

    num_attractors = len(final_states)

    if num_attractors == 0:
        uniqueness = 0.0
        max_basin = 0.0
    else:
        max_basin = max(final_states.values()) / samples
        uniqueness = 1.0 if num_attractors == 1 else max_basin

    return {
        'num_attractors': num_attractors,
        'uniqueness': uniqueness,
        'max_basin_fraction': max_basin,
        'basin_sizes': dict(final_states)
    }

def stability_analysis(N_max=6):
    """
    Comprehensive stability/criticality analysis

    For each (N,K), compute:
    1. L-flow convergence metrics
    2. Constraint saturation
    3. Completion uniqueness
    4. Derivatives/transitions
    """
    results = []

    print("=" * 80)
    print("STABILITY/CRITICALITY ANALYSIS: K(N) = N-2")
    print("=" * 80)
    print("\nHypothesis: K=N-2 marks critical transition or stability boundary")
    print()

    for N in range(3, N_max + 1):
        max_inversions = N * (N - 1) // 2
        K_target = N - 2

        print(f"\nN={N} (K(N)=N-2 = {K_target})")
        print("-" * 60)

        for K in range(0, min(max_inversions + 1, 15)):
            # L-flow dynamics
            lflow = lflow_simulation(N, K, trials=300)

            if lflow is None:
                continue

            # Saturation metrics
            saturation = constraint_saturation_analysis(N, K)

            # Uniqueness test
            uniqueness = completion_uniqueness_test(N, K, samples=150)

            if uniqueness is None:
                continue

            is_critical = (K == K_target)

            result = {
                'N': N,
                'K': K,
                'is_K_N_minus_2': is_critical,
                # L-flow metrics
                'avg_convergence': lflow['avg_convergence'],
                'success_rate': lflow['success_rate'],
                'trajectory_variance': lflow['trajectory_variance'],
                'num_minima': lflow['num_minima'],
                # Saturation metrics
                'constraint_density': saturation['constraint_density'],
                'state_reduction': saturation['state_reduction'],
                'effective_dof': saturation['effective_dof'],
                'V_K': saturation['V_K'],
                # Uniqueness metrics
                'num_attractors': uniqueness['num_attractors'],
                'uniqueness': uniqueness['uniqueness'],
                'max_basin': uniqueness['max_basin_fraction']
            }

            results.append(result)

            marker = " <-- K=N-2 CRITICAL?" if is_critical else ""
            print(f"  K={K:2d}: conv={lflow['avg_convergence']:5.1f}, "
                  f"success={lflow['success_rate']:4.2f}, "
                  f"unique={uniqueness['uniqueness']:4.2f}{marker}")

    return pd.DataFrame(results)

def test_criticality_hypotheses(df):
    """
    Test specific criticality hypotheses:

    1. Sharp transition in convergence rate at K=N-2?
    2. Phase transition in success rate?
    3. Uniqueness changes abruptly?
    4. Derivative/gradient peaks?
    """
    print("\n" + "=" * 80)
    print("CRITICALITY HYPOTHESIS TESTS")
    print("=" * 80)

    hypotheses = {}

    # Hypothesis 1: Convergence rate transition
    print("\n1. Convergence Rate Transition")
    print("-" * 50)

    for N in sorted(df['N'].unique()):
        N_data = df[df['N'] == N].copy()
        K_target = N - 2

        # Compute derivative (finite difference)
        N_data['d_conv_dK'] = N_data['avg_convergence'].diff()

        # Find largest change
        max_change_idx = N_data['d_conv_dK'].abs().idxmax()
        K_at_max_change = N_data.loc[max_change_idx, 'K'] if not np.isnan(max_change_idx) else -1

        # Get value at K=N-2
        target_row = N_data[N_data['K'] == K_target]
        if not target_row.empty:
            change_at_target = target_row['d_conv_dK'].values[0]
        else:
            change_at_target = 0

        match = (K_at_max_change == K_target)
        print(f"  N={N}: max rate change at K={K_at_max_change:.0f}, "
              f"target K={K_target} {'YES' if match else 'NO'}")

    # Hypothesis 2: Success rate phase transition
    print("\n2. Success Rate Phase Transition")
    print("-" * 50)

    success_matches = 0
    success_total = 0

    for N in sorted(df['N'].unique()):
        N_data = df[df['N'] == N].copy()
        K_target = N - 2

        # Check if success rate drops significantly after K=N-2
        before = N_data[N_data['K'] < K_target]['success_rate'].mean() if len(N_data[N_data['K'] < K_target]) > 0 else 0
        at = N_data[N_data['K'] == K_target]['success_rate'].values[0] if len(N_data[N_data['K'] == K_target]) > 0 else 0
        after = N_data[N_data['K'] > K_target]['success_rate'].mean() if len(N_data[N_data['K'] > K_target]) > 0 else 0

        # Is there a drop from before→at or at→after?
        drop_before_to_at = (before - at) > 0.1
        drop_at_to_after = (at - after) > 0.1

        transition = drop_before_to_at or drop_at_to_after
        success_total += 1
        if transition:
            success_matches += 1

        print(f"  N={N}: before={before:.2f}, at={at:.2f}, after={after:.2f} "
              f"{'TRANSITION' if transition else 'no transition'}")

    # Hypothesis 3: Uniqueness criticality
    print("\n3. Uniqueness Criticality")
    print("-" * 50)

    unique_matches = 0
    unique_total = 0

    for N in sorted(df['N'].unique()):
        N_data = df[df['N'] == N].copy()
        K_target = N - 2

        # Check if uniqueness changes at K=N-2
        N_data['d_unique_dK'] = N_data['uniqueness'].diff().abs()

        max_change_idx = N_data['d_unique_dK'].idxmax()
        K_at_max_change = N_data.loc[max_change_idx, 'K'] if not np.isnan(max_change_idx) else -1

        match = abs(K_at_max_change - K_target) <= 1  # Within 1 of target
        unique_total += 1
        if match:
            unique_matches += 1

        print(f"  N={N}: max uniqueness change at K={K_at_max_change:.0f}, "
              f"target K={K_target} {'YES' if match else 'NO'}")

    hypotheses['convergence_transition'] = success_matches / success_total if success_total > 0 else 0
    hypotheses['success_rate_transition'] = success_matches / success_total if success_total > 0 else 0
    hypotheses['uniqueness_transition'] = unique_matches / unique_total if unique_total > 0 else 0

    return hypotheses

def visualize_stability_analysis(df, hypotheses):
    """Create comprehensive stability visualization"""

    fig = plt.figure(figsize=(18, 12))
    gs = fig.add_gridspec(3, 3, hspace=0.3, wspace=0.3)

    colors = plt.cm.tab10(np.linspace(0, 1, 10))
    N_values = sorted(df['N'].unique())

    # Plot 1: Convergence rate vs K
    ax1 = fig.add_subplot(gs[0, 0])
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax1.plot(N_data['K'], N_data['avg_convergence'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax1.plot(target_point['K'], target_point['avg_convergence'], '*',
                    color=colors[i], markersize=20, markeredgecolor='red',
                    markeredgewidth=2)

    ax1.set_xlabel('K', fontsize=11)
    ax1.set_ylabel('Avg Convergence Steps', fontsize=11)
    ax1.set_title('L-Flow Convergence Rate\n(stars = K=N-2)', fontsize=12, fontweight='bold')
    ax1.legend(fontsize=9)
    ax1.grid(True, alpha=0.3)

    # Plot 2: Success rate vs K
    ax2 = fig.add_subplot(gs[0, 1])
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax2.plot(N_data['K'], N_data['success_rate'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax2.plot(target_point['K'], target_point['success_rate'], '*',
                    color=colors[i], markersize=20, markeredgecolor='red',
                    markeredgewidth=2)

    ax2.set_xlabel('K', fontsize=11)
    ax2.set_ylabel('L-Flow Success Rate', fontsize=11)
    ax2.set_title('Completion Success Rate\n(determinism)', fontsize=12, fontweight='bold')
    ax2.legend(fontsize=9)
    ax2.grid(True, alpha=0.3)
    ax2.set_ylim(0, 1.1)

    # Plot 3: Uniqueness vs K
    ax3 = fig.add_subplot(gs[0, 2])
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax3.plot(N_data['K'], N_data['uniqueness'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax3.plot(target_point['K'], target_point['uniqueness'], '*',
                    color=colors[i], markersize=20, markeredgecolor='red',
                    markeredgewidth=2)

    ax3.set_xlabel('K', fontsize=11)
    ax3.set_ylabel('Attractor Uniqueness', fontsize=11)
    ax3.set_title('Unique Completion Fraction', fontsize=12, fontweight='bold')
    ax3.legend(fontsize=9)
    ax3.grid(True, alpha=0.3)
    ax3.set_ylim(0, 1.1)

    # Plot 4: State reduction vs K
    ax4 = fig.add_subplot(gs[1, 0])
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax4.plot(N_data['K'], N_data['state_reduction'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax4.plot(target_point['K'], target_point['state_reduction'], '*',
                    color=colors[i], markersize=20, markeredgecolor='red',
                    markeredgewidth=2)

    ax4.set_xlabel('K', fontsize=11)
    ax4.set_ylabel('|V_K| / N!', fontsize=11)
    ax4.set_title('State Space Reduction', fontsize=12, fontweight='bold')
    ax4.legend(fontsize=9)
    ax4.grid(True, alpha=0.3)
    ax4.set_yscale('log')

    # Plot 5: Effective DOF vs K
    ax5 = fig.add_subplot(gs[1, 1])
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax5.plot(N_data['K'], N_data['effective_dof'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax5.plot(target_point['K'], target_point['effective_dof'], '*',
                    color=colors[i], markersize=20, markeredgecolor='red',
                    markeredgewidth=2)

    ax5.set_xlabel('K', fontsize=11)
    ax5.set_ylabel('log(|V_K|)', fontsize=11)
    ax5.set_title('Effective Degrees of Freedom', fontsize=12, fontweight='bold')
    ax5.legend(fontsize=9)
    ax5.grid(True, alpha=0.3)

    # Plot 6: Number of attractors
    ax6 = fig.add_subplot(gs[1, 2])
    for i, N in enumerate(N_values):
        N_data = df[df['N'] == N]
        K_target = N - 2

        ax6.plot(N_data['K'], N_data['num_attractors'], 'o-', color=colors[i],
                label=f'N={N}', alpha=0.7, markersize=6)

        target_point = N_data[N_data['K'] == K_target]
        if not target_point.empty:
            ax6.plot(target_point['K'], target_point['num_attractors'], '*',
                    color=colors[i], markersize=20, markeredgecolor='red',
                    markeredgewidth=2)

    ax6.set_xlabel('K', fontsize=11)
    ax6.set_ylabel('Number of Attractors', fontsize=11)
    ax6.set_title('Dynamical Complexity', fontsize=12, fontweight='bold')
    ax6.legend(fontsize=9)
    ax6.grid(True, alpha=0.3)

    # Plots 7-9: Detailed phase diagrams for N=4,5,6
    for idx, N in enumerate([4, 5, 6]):
        ax = fig.add_subplot(gs[2, idx])
        N_data = df[df['N'] == N].copy()
        K_target = N - 2

        # Compute gradients
        N_data['d_success'] = N_data['success_rate'].diff().abs()

        ax_twin = ax.twinx()

        l1 = ax.plot(N_data['K'], N_data['success_rate'], 'b-o',
                    label='Success rate', markersize=6, linewidth=2)
        l2 = ax_twin.plot(N_data['K'], N_data['d_success'], 'r-s',
                         label='Rate of change', markersize=5, linewidth=2, alpha=0.7)

        ax.axvline(x=K_target, color='green', linestyle='--', linewidth=2,
                  alpha=0.5, label=f'K=N-2={K_target}')

        ax.set_xlabel('K', fontsize=10)
        ax.set_ylabel('Success Rate', fontsize=10, color='b')
        ax_twin.set_ylabel('d(Success)/dK', fontsize=10, color='r')
        ax.set_title(f'N={N} Phase Diagram', fontsize=11, fontweight='bold')
        ax.tick_params(axis='y', labelcolor='b')
        ax_twin.tick_params(axis='y', labelcolor='r')
        ax.grid(True, alpha=0.3)
        ax.set_ylim(0, 1.1)

        lines = l1 + l2
        labels = [l.get_label() for l in lines]
        ax.legend(lines, labels, fontsize=8, loc='upper right')

    fig.suptitle('Stability/Criticality Analysis: Is K(N)=N-2 a Critical Point?',
                fontsize=16, fontweight='bold', y=0.995)

    return fig

def main():
    """Run stability/criticality analysis"""

    print("\n" + "=" * 80)
    print("REFRAMED HYPOTHESIS: K=N-2 AS CRITICAL/STABILITY POINT")
    print("=" * 80)
    print("\nPrevious optimization tests failed. New framework:")
    print("  - K=N-2 marks phase transition in dynamics")
    print("  - Stability boundary between regimes")
    print("  - Critical point in constraint accumulation")
    print()

    # Run analysis
    df = stability_analysis(N_max=6)

    # Save data
    output_dir = 'outputs' if os.path.exists('outputs') else os.path.join(os.path.dirname(__file__), 'outputs')
    os.makedirs(output_dir, exist_ok=True)

    output_file = os.path.join(output_dir, 'stability_criticality_data.csv')
    df.to_csv(output_file, index=False)
    print(f"\nData saved to: {output_file}")

    # Test hypotheses
    hypotheses = test_criticality_hypotheses(df)

    # Visualize
    print("\nGenerating visualization...")
    fig = visualize_stability_analysis(df, hypotheses)

    plot_file = os.path.join(output_dir, 'stability_criticality_analysis.png')
    fig.savefig(plot_file, dpi=150, bbox_inches='tight')
    print(f"Plot saved to: {plot_file}")
    plt.show()

    # Final verdict
    print("\n" + "=" * 80)
    print("FINAL VERDICT: CRITICALITY HYPOTHESIS")
    print("=" * 80)

    avg_score = np.mean(list(hypotheses.values()))

    if avg_score >= 0.7:
        print(f"\nHYPOTHESIS SUPPORTED (score: {avg_score:.1%})")
        print("\nK=N-2 shows critical/stability behavior:")
        for key, val in hypotheses.items():
            if val >= 0.5:
                print(f"  - {key}: {val:.1%} match")
    elif avg_score >= 0.4:
        print(f"\nHYPOTHESIS PARTIALLY SUPPORTED (score: {avg_score:.1%})")
        print("\nSome evidence of critical behavior:")
        for key, val in hypotheses.items():
            print(f"  - {key}: {val:.1%}")
    else:
        print(f"\nHYPOTHESIS WEAK (score: {avg_score:.1%})")
        print("\nLimited evidence for critical point at K=N-2")

    # Save summary
    import json
    summary = {
        'verdict': 'SUPPORTED' if avg_score >= 0.7 else 'PARTIAL' if avg_score >= 0.4 else 'WEAK',
        'avg_score': avg_score,
        'hypotheses': hypotheses
    }

    summary_file = os.path.join(output_dir, 'stability_criticality_summary.json')
    with open(summary_file, 'w') as f:
        json.dump(summary, f, indent=2)

    print(f"\nSummary saved to: {summary_file}")
    print("\n" + "=" * 80)
    print("Analysis complete!")
    print("=" * 80)

if __name__ == "__main__":
    main()
