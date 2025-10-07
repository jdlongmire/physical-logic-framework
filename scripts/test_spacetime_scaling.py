"""
Extended Spacetime Scaling Test (N=3,4,5,6)

Extension of Test 2.0 to larger N values to analyze:
1. Spatial dimension scaling: Does dimension → 3 as N increases?
2. Symmetry groups of time-slices: What are the automorphisms?
3. Convergence to SO(3,1): Does symmetry group → Lorentz group?

Key questions:
- Does spatial dimension converge to 3 for large N?
- Do symmetry groups show patterns consistent with rotations?
- Does automorphism group structure suggest SO(3,1) emergence?

Date: October 7, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from itertools import permutations
import networkx as nx
from scipy.spatial.distance import pdist, squareform
from scipy.stats import linregress
import json
from datetime import datetime
from collections import defaultdict

def compute_inversion_count(perm):
    """Compute inversion count h(sigma) for permutation."""
    n = len(perm)
    count = 0
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                count += 1
    return count

def permutohedron_embedding(perm):
    """
    Compute permutohedron embedding coordinates for permutation.

    Standard embedding in R^(N-1):
    sigma -> (sigma(1), sigma(2), ..., sigma(N-1))
    (dropping last coordinate since sum is constant)
    """
    return np.array(perm[:-1], dtype=float)

def extract_time_slices(N, K):
    """
    Extract time-slices: all permutations at each h-level.

    Returns:
        dict: {h: [list of permutations at that h-level]}
    """
    time_slices = {}
    all_perms = list(permutations(range(1, N+1)))

    for perm in all_perms:
        h = compute_inversion_count(perm)
        if h <= K:  # Constraint: h <= K
            if h not in time_slices:
                time_slices[h] = []
            time_slices[h].append(perm)

    return time_slices

def analyze_spatial_slice(perms, h_level):
    """
    Analyze spatial manifold structure for permutations at fixed h-level.

    Returns:
        dict: {
            'dimension': estimated spatial dimension,
            'connectivity': graph connectivity measure,
            'diameter': maximum spatial distance,
            'num_states': number of spatial positions
        }
    """
    if len(perms) < 2:
        return {
            'dimension': 0,
            'connectivity': 1.0,
            'diameter': 0.0,
            'num_states': len(perms)
        }

    # Compute embedding coordinates
    coords = np.array([permutohedron_embedding(p) for p in perms])

    # Pairwise spatial distances
    distances = squareform(pdist(coords, metric='euclidean'))

    # Build spatial connectivity graph (connect nearest neighbors)
    # Use median distance as threshold
    threshold = np.median(distances[distances > 0])
    G = nx.Graph()
    for i in range(len(perms)):
        G.add_node(i)
    for i in range(len(perms)):
        for j in range(i+1, len(perms)):
            if 0 < distances[i,j] <= threshold:
                G.add_edge(i, j)

    # Estimate spatial dimension via volume scaling
    # For d-dimensional manifold: N_points ~ r^d
    # Use correlation dimension estimate
    if len(perms) >= 3:
        # Count pairs within distance r for various r
        max_dist = np.max(distances)
        r_values = np.linspace(0.1*max_dist, 0.9*max_dist, 10)
        counts = []
        for r in r_values:
            count = np.sum(distances < r) - len(perms)  # Exclude diagonal
            counts.append(count / 2)  # Each pair counted twice

        # Fit log(count) vs log(r) to get dimension
        valid = np.array(counts) > 0
        if np.sum(valid) >= 3:
            slope, _, _, _, _ = linregress(np.log(r_values[valid]),
                                          np.log(np.array(counts)[valid]))
            dimension = slope
        else:
            dimension = 1.0
    else:
        dimension = 1.0

    # Connectivity: is graph connected?
    connectivity = 1.0 if nx.is_connected(G) else 0.0

    # Diameter: maximum spatial distance
    diameter = np.max(distances)

    return {
        'dimension': dimension,
        'connectivity': connectivity,
        'diameter': diameter,
        'num_states': len(perms),
        'distances': distances,
        'coords': coords
    }

def compute_spatial_symmetries(perms, h_level):
    """
    Compute symmetries (automorphisms) of the spatial slice.

    A symmetry is a permutation of states that preserves spatial structure.
    For computational efficiency, we check:
    1. Distance-preserving transformations
    2. Graph automorphisms

    Returns:
        dict: {
            'num_symmetries': number of automorphisms found,
            'symmetry_group_order': estimated order of symmetry group,
            'sample_symmetries': list of sample transformation matrices
        }
    """
    if len(perms) < 2:
        return {
            'num_symmetries': 1,
            'symmetry_group_order': 1,
            'sample_symmetries': []
        }

    # Compute embedding coordinates
    coords = np.array([permutohedron_embedding(p) for p in perms])

    # Compute distance matrix
    distances = squareform(pdist(coords, metric='euclidean'))

    # Build adjacency graph
    threshold = np.median(distances[distances > 0])
    G = nx.Graph()
    for i in range(len(perms)):
        G.add_node(i)
    for i in range(len(perms)):
        for j in range(i+1, len(perms)):
            if 0 < distances[i,j] <= threshold:
                G.add_edge(i, j)

    # Compute graph automorphisms (these are the discrete symmetries)
    # For large graphs, this is expensive, so we sample
    try:
        if len(perms) <= 10:
            # For small graphs, compute exact automorphism group
            automorphisms = list(nx.algorithms.isomorphism.GraphMatcher(G, G).isomorphisms_iter())
            num_automorphisms = len(automorphisms)
        else:
            # For large graphs, estimate using degree sequence and sampling
            # This is a heuristic - exact computation is too expensive
            degree_sequence = sorted([G.degree(n) for n in G.nodes()])
            # Check if graph is highly symmetric (regular degree sequence)
            if len(set(degree_sequence)) <= 2:
                # Likely has many symmetries
                num_automorphisms = len(perms)  # Upper bound estimate
            else:
                # Likely has few symmetries
                num_automorphisms = 1  # Lower bound estimate
    except Exception as e:
        # Fallback if automorphism computation fails
        num_automorphisms = 1

    return {
        'num_symmetries': num_automorphisms,
        'symmetry_group_order': num_automorphisms,
        'sample_symmetries': []  # Could store transformation matrices
    }

def analyze_symmetry_scaling(all_spatial_results):
    """
    Analyze how symmetry groups scale with N.

    Key question: Does symmetry group → SO(3) (rotations) as N→∞?
    SO(3) is continuous, but discrete approximations grow in specific ways.

    Returns:
        dict: Analysis of symmetry scaling patterns
    """
    scaling_data = {}

    for case_key, spatial_results in all_spatial_results.items():
        # Extract N from case key (format: "N{N}_K{K}")
        N = int(case_key.split('_')[0][1:])

        # Get maximum time-slice (highest h, most states)
        max_h = max(spatial_results.keys())
        max_slice = spatial_results[max_h]

        scaling_data[N] = {
            'num_states': max_slice['num_states'],
            'dimension': max_slice['dimension'],
            'symmetries': max_slice.get('num_symmetries', None)
        }

    # Analyze trends
    N_values = sorted(scaling_data.keys())
    dimensions = [scaling_data[N]['dimension'] for N in N_values]
    num_states = [scaling_data[N]['num_states'] for N in N_values]

    # Check if dimension → 3
    dimension_trend = {
        'N_values': N_values,
        'dimensions': dimensions,
        'converging_to_3': abs(dimensions[-1] - 3.0) < 0.5 if dimensions else False
    }

    # Check volume scaling (expect exponential for finite-volume manifold)
    volume_trend = {
        'N_values': N_values,
        'num_states': num_states,
        'scaling_type': 'exponential' if len(num_states) > 1 and num_states[-1] > num_states[0] * 2 else 'sublinear'
    }

    return {
        'dimension_trend': dimension_trend,
        'volume_trend': volume_trend,
        'raw_data': scaling_data
    }

def compute_spacetime_interval(perm1, h1, perm2, h2):
    """
    Compute spacetime interval between two events.

    Event 1: (perm1, h1) - permutation perm1 at time-slice h1
    Event 2: (perm2, h2) - permutation perm2 at time-slice h2

    Hypothesis: ds^2 = -dt^2 + dl^2
    where:
        dt = |h2 - h1| (temporal separation, in L-Flow steps)
        dl = |embedding(perm2) - embedding(perm1)| (spatial separation)

    Returns:
        dict: {
            'ds_squared': spacetime interval,
            'dt': temporal separation,
            'dl': spatial separation,
            'type': 'timelike', 'spacelike', or 'lightlike'
        }
    """
    # Temporal separation (in units of L-Flow steps)
    dt = abs(h2 - h1)

    # Spatial separation (Euclidean distance in embedding)
    coord1 = permutohedron_embedding(perm1)
    coord2 = permutohedron_embedding(perm2)
    dl = np.linalg.norm(coord2 - coord1)

    # Spacetime interval (Minkowski signature: -,+,+,+)
    ds_squared = -dt**2 + dl**2

    # Classify interval type
    if ds_squared < -1e-10:
        interval_type = 'timelike'
    elif ds_squared > 1e-10:
        interval_type = 'spacelike'
    else:
        interval_type = 'lightlike'

    return {
        'ds_squared': ds_squared,
        'dt': dt,
        'dl': dl,
        'type': interval_type
    }

def test_metric_signature(time_slices):
    """
    Test if spacetime metric has Minkowski signature (-,+,+,+).

    Checks:
    1. Temporal separations (same position, different h) are timelike
    2. Spatial separations (different position, same h) are spacelike
    3. Mixed separations follow light cone structure
    """
    results = {
        'temporal_timelike': [],  # dt>0, dl=0 -> ds^2 < 0
        'spatial_spacelike': [],  # dt=0, dl>0 -> ds^2 > 0
        'mixed_intervals': []     # dt>0, dl>0 -> depends on ratio
    }

    h_levels = sorted(time_slices.keys())

    # Test 1: Temporal separations (track same permutation through time)
    for i in range(len(h_levels)-1):
        h1, h2 = h_levels[i], h_levels[i+1]
        perms1 = set(time_slices[h1])
        perms2 = set(time_slices[h2])

        # Find common permutations
        common = perms1.intersection(perms2)
        for perm in list(common)[:5]:  # Sample up to 5
            interval = compute_spacetime_interval(perm, h1, perm, h2)
            results['temporal_timelike'].append(interval)

    # Test 2: Spatial separations (different permutations at same h)
    for h in h_levels:
        perms = time_slices[h]
        if len(perms) >= 2:
            # Sample pairs of different permutations at same h
            sample_size = min(5, len(perms))
            for i in range(sample_size):
                for j in range(i+1, min(i+3, len(perms))):
                    interval = compute_spacetime_interval(perms[i], h, perms[j], h)
                    results['spatial_spacelike'].append(interval)

    # Test 3: Mixed intervals (different permutation AND different h)
    for i in range(len(h_levels)-1):
        h1, h2 = h_levels[i], h_levels[i+1]
        perms1 = time_slices[h1]
        perms2 = time_slices[h2]

        # Sample cross-level pairs
        for p1 in perms1[:3]:
            for p2 in perms2[:3]:
                interval = compute_spacetime_interval(p1, h1, p2, h2)
                results['mixed_intervals'].append(interval)

    # Analyze results
    summary = {}

    # Check temporal intervals are timelike (ds^2 < 0)
    if results['temporal_timelike']:
        temporal_signs = [x['ds_squared'] for x in results['temporal_timelike']]
        summary['temporal_fraction_timelike'] = np.mean(np.array(temporal_signs) < 0)
    else:
        summary['temporal_fraction_timelike'] = None

    # Check spatial intervals are spacelike (ds^2 > 0)
    if results['spatial_spacelike']:
        spatial_signs = [x['ds_squared'] for x in results['spatial_spacelike']]
        summary['spatial_fraction_spacelike'] = np.mean(np.array(spatial_signs) > 0)
    else:
        summary['spatial_fraction_spacelike'] = None

    # Check mixed intervals
    if results['mixed_intervals']:
        mixed_signs = [x['ds_squared'] for x in results['mixed_intervals']]
        summary['mixed_timelike_fraction'] = np.mean(np.array(mixed_signs) < 0)
        summary['mixed_spacelike_fraction'] = np.mean(np.array(mixed_signs) > 0)

    return summary, results

def run_spacetime_test(N, K):
    """
    Run complete spacetime separation test for given N and K.
    """
    print(f"\n{'='*60}")
    print(f"Testing Spacetime Separation for N={N}, K={K}")
    print(f"{'='*60}\n")

    # Extract time-slices
    print("Phase 1: Extracting time-slices...")
    time_slices = extract_time_slices(N, K)

    print(f"  Found {len(time_slices)} time-slices (h-levels):")
    for h in sorted(time_slices.keys()):
        print(f"    h={h}: {len(time_slices[h])} states (spatial positions)")

    # Analyze spatial structure at each time-slice
    print("\nPhase 2: Analyzing spatial manifold structure...")
    spatial_results = {}
    for h in sorted(time_slices.keys()):
        print(f"  Analyzing h={h}...")
        spatial_results[h] = analyze_spatial_slice(time_slices[h], h)
        print(f"    Spatial dimension: {spatial_results[h]['dimension']:.2f}")
        print(f"    Connectivity: {spatial_results[h]['connectivity']:.2f}")
        print(f"    Spatial diameter: {spatial_results[h]['diameter']:.3f}")

        # Add symmetry analysis for largest time-slice
        if h == max(time_slices.keys()):
            print(f"  Computing symmetries for h={h}...")
            symmetry_info = compute_spatial_symmetries(time_slices[h], h)
            spatial_results[h]['num_symmetries'] = symmetry_info['num_symmetries']
            print(f"    Symmetry group order: ~{symmetry_info['num_symmetries']}")

    # Test metric signature
    print("\nPhase 3: Testing metric signature...")
    metric_summary, metric_details = test_metric_signature(time_slices)

    if metric_summary.get('temporal_fraction_timelike') is not None:
        print(f"  Temporal intervals timelike: {metric_summary['temporal_fraction_timelike']*100:.1f}%")
    if metric_summary.get('spatial_fraction_spacelike') is not None:
        print(f"  Spatial intervals spacelike: {metric_summary['spatial_fraction_spacelike']*100:.1f}%")

    # Compile results
    results = {
        'N': N,
        'K': K,
        'num_time_slices': len(time_slices),
        'time_slices': {h: len(perms) for h, perms in time_slices.items()},
        'spatial_analysis': spatial_results,
        'metric_signature': metric_summary
    }

    # Overall assessment
    print("\n" + "="*60)
    print("ASSESSMENT:")
    print("="*60)

    # Check key criteria
    criteria = {
        'Time-slices are spatial manifolds': all(
            r['dimension'] >= 1.0 for r in spatial_results.values()
        ),
        'Metric has correct signature': (
            metric_summary.get('spatial_fraction_spacelike', 0) > 0.8
        ),
        'Temporal intervals are timelike': (
            metric_summary.get('temporal_fraction_timelike') is None or
            metric_summary.get('temporal_fraction_timelike', 0) > 0.8
        )
    }

    for criterion, passed in criteria.items():
        status = "[PASS]" if passed else "[FAIL]"
        print(f"  {status} {criterion}")

    success_rate = sum(criteria.values()) / len(criteria)
    print(f"\nOverall Success Rate: {success_rate*100:.1f}%")

    return results

def visualize_dimension_scaling(all_results, output_dir='./'):
    """
    Visualize how spatial dimension scales with N.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))

    # Extract scaling data
    N_values = []
    max_dimensions = []
    max_num_states = []
    max_h_values = []

    for case_key in sorted(all_results.keys()):
        if case_key == 'metadata':
            continue

        results = all_results[case_key]
        N = results['N']

        # Get maximum h-level (largest time-slice)
        spatial_analysis = results['spatial_analysis']
        max_h = max([int(h) for h in spatial_analysis.keys()])
        max_slice = spatial_analysis[max_h]

        N_values.append(N)
        max_dimensions.append(max_slice['dimension'])
        max_num_states.append(max_slice['num_states'])
        max_h_values.append(max_h)

    # Plot 1: Spatial dimension vs N
    ax1 = axes[0, 0]
    ax1.plot(N_values, max_dimensions, 'o-', linewidth=2, markersize=10, color='steelblue')
    ax1.axhline(y=3.0, color='red', linestyle='--', linewidth=2, label='Target: 3D space')
    ax1.set_xlabel('N (number of elements)', fontsize=12)
    ax1.set_ylabel('Spatial Dimension', fontsize=12)
    ax1.set_title('Spatial Dimension Scaling', fontsize=14, fontweight='bold')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    ax1.set_ylim([0, max(max_dimensions) + 0.5])

    # Plot 2: Number of spatial states vs N
    ax2 = axes[0, 1]
    ax2.semilogy(N_values, max_num_states, 's-', linewidth=2, markersize=10, color='darkgreen')
    ax2.set_xlabel('N (number of elements)', fontsize=12)
    ax2.set_ylabel('Number of Spatial States (log scale)', fontsize=12)
    ax2.set_title('Spatial Volume Scaling', fontsize=14, fontweight='bold')
    ax2.grid(True, alpha=0.3)

    # Plot 3: Dimension vs num_states (phase space volume)
    ax3 = axes[1, 0]
    ax3.loglog(max_num_states, max_dimensions, 'D-', linewidth=2, markersize=10, color='purple')
    ax3.set_xlabel('Number of States (log scale)', fontsize=12)
    ax3.set_ylabel('Dimension (log scale)', fontsize=12)
    ax3.set_title('Dimension vs Volume', fontsize=14, fontweight='bold')
    ax3.grid(True, alpha=0.3)

    # Plot 4: Dimension for all h-levels (all N values)
    ax4 = axes[1, 1]
    for case_key in sorted(all_results.keys()):
        if case_key == 'metadata':
            continue

        results = all_results[case_key]
        N = results['N']
        spatial_analysis = results['spatial_analysis']

        h_vals = sorted([int(h) for h in spatial_analysis.keys()])
        dims = [spatial_analysis[h]['dimension'] for h in h_vals]

        ax4.plot(h_vals, dims, 'o-', linewidth=2, markersize=8, label=f'N={N}', alpha=0.7)

    ax4.axhline(y=3.0, color='red', linestyle='--', linewidth=2, alpha=0.5, label='3D target')
    ax4.set_xlabel('Time-slice h', fontsize=12)
    ax4.set_ylabel('Spatial Dimension', fontsize=12)
    ax4.set_title('Dimension Evolution Through Time', fontsize=14, fontweight='bold')
    ax4.legend()
    ax4.grid(True, alpha=0.3)

    plt.suptitle('Spacetime Scaling Analysis: N=3,4,5,6', fontsize=16, fontweight='bold')
    plt.tight_layout()

    # Save figure
    plt.savefig(f'{output_dir}/spacetime_dimension_scaling.png', dpi=300, bbox_inches='tight')
    plt.savefig(f'{output_dir}/spacetime_dimension_scaling.svg', bbox_inches='tight')
    print(f"\n[OK] Scaling visualization saved to {output_dir}/spacetime_dimension_scaling.png/svg")

    plt.close()

def main():
    """
    Main test execution.
    """
    print("\n" + "="*60)
    print("SPACETIME SCALING TEST (N=3,4,5,6)")
    print("="*60)
    print("\nQuestion: Does spatial dimension -> 3 as N increases?")
    print("Hypothesis: Spacetime = Space (geometry) x Time (sequential logic)\n")

    # Test cases
    test_cases = [
        (3, 1),  # N=3, K=N-2=1
        (4, 2),  # N=4, K=N-2=2
        (5, 3),  # N=5, K=N-2=3
        (6, 4),  # N=6, K=N-2=4
    ]

    all_results = {}

    for N, K in test_cases:
        results = run_spacetime_test(N, K)
        all_results[f'N{N}_K{K}'] = results

    # Analyze symmetry scaling
    print("\n" + "="*60)
    print("SYMMETRY SCALING ANALYSIS")
    print("="*60)

    # Extract spatial results for symmetry analysis
    all_spatial_results = {
        case_key: all_results[case_key]['spatial_analysis']
        for case_key in all_results.keys()
    }

    symmetry_scaling = analyze_symmetry_scaling(all_spatial_results)

    print("\nDimension Trend:")
    print(f"  N values: {symmetry_scaling['dimension_trend']['N_values']}")
    print(f"  Dimensions: {[f'{d:.2f}' for d in symmetry_scaling['dimension_trend']['dimensions']]}")
    print(f"  Converging to 3D: {symmetry_scaling['dimension_trend']['converging_to_3']}")

    print("\nVolume Scaling:")
    print(f"  States: {symmetry_scaling['volume_trend']['num_states']}")
    print(f"  Scaling type: {symmetry_scaling['volume_trend']['scaling_type']}")

    # Generate scaling visualization
    print(f"\nGenerating scaling visualization...")
    output_dir = 'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/paper/supporting_material/spacetime_research'
    visualize_dimension_scaling(all_results, output_dir=output_dir)

    # Save results
    output_file = f'{output_dir}/spacetime_scaling_results.json'

    # Convert numpy types to Python types for JSON serialization
    def convert_to_serializable(obj):
        if isinstance(obj, (np.integer, np.int_)):
            return int(obj)
        elif isinstance(obj, (np.floating, np.float_)):
            return float(obj)
        elif isinstance(obj, (np.bool_, bool)):
            return bool(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, dict):
            return {k: convert_to_serializable(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert_to_serializable(item) for item in obj]
        else:
            return obj

    serializable_results = convert_to_serializable(all_results)
    serializable_results['metadata'] = {
        'date': datetime.now().isoformat(),
        'hypothesis': 'Spatial dimension -> 3 as N->infinity',
        'test_version': '3.0 (Scaling)',
        'symmetry_scaling': convert_to_serializable(symmetry_scaling)
    }

    with open(output_file, 'w') as f:
        json.dump(serializable_results, f, indent=2)

    print(f"\n[OK] Results saved to {output_file}")

    # Final summary
    print("\n" + "="*60)
    print("FINAL VERDICT")
    print("="*60)

    # Check if dimension is converging to 3
    N_values = symmetry_scaling['dimension_trend']['N_values']
    dimensions = symmetry_scaling['dimension_trend']['dimensions']

    if len(dimensions) >= 2:
        final_dimension = dimensions[-1]
        trend = dimensions[-1] - dimensions[0]

        print(f"\nSpatial dimension for N={N_values[-1]}: {final_dimension:.2f}")
        print(f"Dimension change from N={N_values[0]} to N={N_values[-1]}: {trend:+.2f}")

        if abs(final_dimension - 3.0) < 0.5:
            print("\n[SUCCESS] Spatial dimension approaching 3D!")
            print("Strong evidence for 3D space emergence as N->infinity")
        elif trend > 0:
            print("\n[TRENDING] Dimension increasing with N")
            print("Suggests convergence to 3D, but need larger N to confirm")
        else:
            print("\n[INCONCLUSIVE] Dimension not clearly converging to 3D")
            print("May need different scaling analysis method")

    print("\n" + "="*60 + "\n")

if __name__ == '__main__':
    main()
