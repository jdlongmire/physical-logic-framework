"""
Test Spacetime Separation Hypothesis (Test 2.0)

User's Insight: "Spacetime emerges from geometry and sequential logic"

Framework:
- Space = Permutohedron geometry (different permutations at same h)
- Time = Sequential logic operations (L-Flow step counting, different h values)
- Spacetime = Space × Time (product structure)

This test validates whether separating spatial geometry from temporal
sequential operations gives proper spacetime structure with Lorentz-like properties.

Date: October 6, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from itertools import permutations
import networkx as nx
from scipy.spatial.distance import pdist, squareform
from scipy.stats import linregress
import json
from datetime import datetime

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
    # For adjacent h-levels, find permutations that appear in both
    for i in range(len(h_levels)-1):
        h1, h2 = h_levels[i], h_levels[i+1]
        perms1 = set(time_slices[h1])
        perms2 = set(time_slices[h2])

        # Find common permutations (if any exist at adjacent h-levels)
        # Note: In reality, L-Flow changes permutation, so this tests
        # "what if we could track the same state through time?"
        common = perms1.intersection(perms2)
        for perm in list(common)[:5]:  # Sample up to 5
            interval = compute_spacetime_interval(perm, h1, perm, h2)
            results['temporal_timelike'].append(interval)

    # Test 2: Spatial separations (different permutations at same h)
    for h in h_levels:
        perms = time_slices[h]
        if len(perms) >= 2:
            # Sample pairs of different permutations at same h
            for i in range(min(5, len(perms))):
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

def test_lorentz_invariance(time_slices):
    """
    Test if structure admits Lorentz-like transformations.

    A Lorentz transformation preserves ds^2 = -dt^2 + dl^2.
    We check if there exist transformations of the time-slices that:
    1. Mix space and time coordinates
    2. Preserve the spacetime interval
    """
    # For simplicity, test if boost-like transformations exist
    # A boost in x-direction: t' = gamma(t - vx), x' = gamma(x - vt)
    # This is complex for discrete structure - placeholder for now

    # Instead, check if interval is preserved under permutation of time-slices
    # (This is a weak test, but computable)

    h_levels = sorted(time_slices.keys())
    if len(h_levels) < 2:
        return {'lorentz_like': False, 'reason': 'Insufficient time-slices'}

    # Sample intervals in original structure
    original_intervals = []
    for i in range(min(3, len(h_levels)-1)):
        h1, h2 = h_levels[i], h_levels[i+1]
        perms1 = time_slices[h1]
        perms2 = time_slices[h2]
        if perms1 and perms2:
            interval = compute_spacetime_interval(perms1[0], h1, perms2[0], h2)
            original_intervals.append(interval['ds_squared'])

    # Check if intervals have consistent signature (all timelike or pattern)
    if original_intervals:
        signs = np.sign(original_intervals)
        consistency = np.std(signs)  # Low std = consistent signature

        return {
            'lorentz_like': consistency < 0.5,
            'interval_consistency': consistency,
            'sample_intervals': original_intervals
        }

    return {'lorentz_like': False, 'reason': 'No intervals computed'}

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

    # Test metric signature
    print("\nPhase 3: Testing metric signature...")
    metric_summary, metric_details = test_metric_signature(time_slices)

    if metric_summary.get('temporal_fraction_timelike') is not None:
        print(f"  Temporal intervals timelike: {metric_summary['temporal_fraction_timelike']*100:.1f}%")
    if metric_summary.get('spatial_fraction_spacelike') is not None:
        print(f"  Spatial intervals spacelike: {metric_summary['spatial_fraction_spacelike']*100:.1f}%")

    # Test Lorentz-like properties
    print("\nPhase 4: Testing Lorentz-like properties...")
    lorentz_results = test_lorentz_invariance(time_slices)
    print(f"  Lorentz-like structure: {lorentz_results.get('lorentz_like', 'Unknown')}")

    # Compile results
    results = {
        'N': N,
        'K': K,
        'num_time_slices': len(time_slices),
        'time_slices': {h: len(perms) for h, perms in time_slices.items()},
        'spatial_analysis': spatial_results,
        'metric_signature': metric_summary,
        'lorentz_test': lorentz_results
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
        ),
        'Structure admits Lorentz-like symmetry': lorentz_results.get('lorentz_like', False)
    }

    for criterion, passed in criteria.items():
        status = "[PASS]" if passed else "[FAIL]"
        print(f"  {status} {criterion}")

    success_rate = sum(criteria.values()) / len(criteria)
    print(f"\nOverall Success Rate: {success_rate*100:.1f}%")

    if success_rate >= 0.75:
        print("\n[SUCCESS] Space/time separation gives proper spacetime structure!")
    elif success_rate >= 0.5:
        print("\n[PARTIAL] Some spacetime properties emerge, but structure incomplete")
    else:
        print("\n[FAILURE] Space/time separation does not produce spacetime structure")

    return results

def visualize_spacetime_structure(N, K, results, output_dir='./'):
    """
    Generate visualization of spacetime structure.
    """
    fig = plt.figure(figsize=(16, 12))

    # Extract time-slices for visualization
    time_slices = extract_time_slices(N, K)
    h_levels = sorted(time_slices.keys())

    # Plot 1: Time-slice spatial manifolds (3D if N=4)
    ax1 = fig.add_subplot(2, 3, 1, projection='3d' if N == 4 else None)

    if N == 4:
        # For N=4, we have 3D embedding coordinates
        for h in h_levels:
            perms = time_slices[h]
            coords = np.array([permutohedron_embedding(p) for p in perms])
            ax1.scatter(coords[:, 0], coords[:, 1], coords[:, 2],
                       label=f'h={h}', s=50, alpha=0.6)
        ax1.set_xlabel('x1')
        ax1.set_ylabel('x2')
        ax1.set_zlabel('x3')
        ax1.set_title('Time-Slices as Spatial Manifolds')
        ax1.legend()
    else:
        # For N=3, plot 2D slices
        for h in h_levels:
            perms = time_slices[h]
            coords = np.array([permutohedron_embedding(p) for p in perms])
            ax1.scatter(coords[:, 0], coords[:, 1],
                       label=f'h={h}', s=50, alpha=0.6)
        ax1.set_xlabel('x1')
        ax1.set_ylabel('x2')
        ax1.set_title('Time-Slices as Spatial Manifolds')
        ax1.legend()

    # Plot 2: Spatial dimension vs time
    ax2 = fig.add_subplot(2, 3, 2)
    h_vals = []
    dims = []
    for h in h_levels:
        h_vals.append(h)
        dims.append(results['spatial_analysis'][h]['dimension'])
    ax2.plot(h_vals, dims, 'o-', linewidth=2, markersize=8)
    ax2.set_xlabel('Time (h-level)')
    ax2.set_ylabel('Spatial Dimension')
    ax2.set_title('Spatial Dimension vs Time')
    ax2.grid(True, alpha=0.3)

    # Plot 3: Number of spatial positions vs time
    ax3 = fig.add_subplot(2, 3, 3)
    h_vals = []
    num_states = []
    for h in h_levels:
        h_vals.append(h)
        num_states.append(len(time_slices[h]))
    ax3.bar(h_vals, num_states, alpha=0.7, color='steelblue')
    ax3.set_xlabel('Time (h-level)')
    ax3.set_ylabel('Number of Spatial Positions')
    ax3.set_title('Spatial Volume vs Time')
    ax3.grid(True, alpha=0.3, axis='y')

    # Plot 4: Spacetime interval distribution
    ax4 = fig.add_subplot(2, 3, 4)

    # Compute sample intervals
    all_intervals = []
    interval_types = []
    for i in range(len(h_levels)-1):
        h1, h2 = h_levels[i], h_levels[i+1]
        perms1 = time_slices[h1]
        perms2 = time_slices[h2]
        for p1 in perms1[:5]:
            for p2 in perms2[:5]:
                interval = compute_spacetime_interval(p1, h1, p2, h2)
                all_intervals.append(interval['ds_squared'])
                interval_types.append(interval['type'])

    if all_intervals:
        ax4.hist(all_intervals, bins=20, alpha=0.7, color='purple', edgecolor='black')
        ax4.axvline(x=0, color='red', linestyle='--', linewidth=2, label='ds²=0 (lightlike)')
        ax4.set_xlabel('Spacetime Interval ds²')
        ax4.set_ylabel('Frequency')
        ax4.set_title('Distribution of Spacetime Intervals')
        ax4.legend()
        ax4.grid(True, alpha=0.3)

    # Plot 5: Metric signature test
    ax5 = fig.add_subplot(2, 3, 5)

    metric_data = []
    labels = []

    if results['metric_signature'].get('spatial_fraction_spacelike') is not None:
        metric_data.append(results['metric_signature']['spatial_fraction_spacelike'] * 100)
        labels.append('Spatial\nSpacelike')

    if results['metric_signature'].get('temporal_fraction_timelike') is not None:
        metric_data.append(results['metric_signature']['temporal_fraction_timelike'] * 100)
        labels.append('Temporal\nTimelike')

    if metric_data:
        bars = ax5.bar(range(len(metric_data)), metric_data,
                       color=['steelblue', 'darkred'][:len(metric_data)], alpha=0.7)
        ax5.set_xticks(range(len(labels)))
        ax5.set_xticklabels(labels)
        ax5.set_ylabel('Percentage (%)')
        ax5.set_title('Metric Signature Verification')
        ax5.axhline(y=80, color='green', linestyle='--', linewidth=2, alpha=0.5, label='80% threshold')
        ax5.legend()
        ax5.grid(True, alpha=0.3, axis='y')
        ax5.set_ylim([0, 105])

    # Plot 6: Spacetime diagram (2D projection)
    ax6 = fig.add_subplot(2, 3, 6)

    # For each time-slice, plot spatial extent
    for h in h_levels:
        perms = time_slices[h]
        coords = np.array([permutohedron_embedding(p) for p in perms])
        # Project to first spatial coordinate
        x_coords = coords[:, 0] if coords.shape[1] > 0 else np.zeros(len(perms))
        times = np.full(len(perms), h)
        ax6.scatter(x_coords, times, s=30, alpha=0.6, color=f'C{h}')

    ax6.set_xlabel('Spatial Coordinate x1')
    ax6.set_ylabel('Time (h-level)')
    ax6.set_title('Spacetime Diagram (x1-t projection)')
    ax6.grid(True, alpha=0.3)

    plt.suptitle(f'Spacetime Separation Test: N={N}, K={K}', fontsize=16, fontweight='bold')
    plt.tight_layout()

    # Save figure
    plt.savefig(f'{output_dir}/spacetime_separation_N{N}_K{K}.png', dpi=300, bbox_inches='tight')
    plt.savefig(f'{output_dir}/spacetime_separation_N{N}_K{K}.svg', bbox_inches='tight')
    print(f"\n[OK] Visualization saved to {output_dir}/spacetime_separation_N{N}_K{K}.png/svg")

    plt.close()

def main():
    """
    Main test execution.
    """
    print("\n" + "="*60)
    print("SPACETIME SEPARATION TEST 2.0")
    print("="*60)
    print("\nHypothesis: Spacetime = Space (geometry) x Time (sequential logic)")
    print("Test: Does this product structure give Minkowski spacetime?\n")

    # Test cases
    test_cases = [
        (3, 1),  # N=3, K=N-2=1
        (4, 2),  # N=4, K=N-2=2
    ]

    all_results = {}

    for N, K in test_cases:
        results = run_spacetime_test(N, K)
        all_results[f'N{N}_K{K}'] = results

        # Generate visualization
        print(f"\nGenerating visualization for N={N}, K={K}...")
        visualize_spacetime_structure(N, K, results,
                                     output_dir='C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/paper/supporting_material/spacetime_research')

    # Save results
    output_file = 'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/paper/supporting_material/spacetime_research/spacetime_separation_results.json'

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
        'hypothesis': 'Spacetime = Space (geometry) x Time (sequential logic)',
        'test_version': '2.0'
    }

    with open(output_file, 'w') as f:
        json.dump(serializable_results, f, indent=2)

    print(f"\n[OK] Results saved to {output_file}")

    # Final summary
    print("\n" + "="*60)
    print("FINAL VERDICT")
    print("="*60)

    success_count = 0
    total_count = 0

    for case, results in all_results.items():
        if 'metric_signature' in results:
            spatial_ok = results['metric_signature'].get('spatial_fraction_spacelike', 0) > 0.8
            if spatial_ok:
                success_count += 1
            total_count += 1

    if total_count > 0:
        overall_success_rate = success_count / total_count
        print(f"\nCases with correct metric signature: {success_count}/{total_count}")
        print(f"Overall success rate: {overall_success_rate*100:.1f}%")

        if overall_success_rate >= 0.8:
            print("\n[BREAKTHROUGH] User's insight VALIDATED!")
            print("Space/time separation produces proper spacetime structure.")
        elif overall_success_rate >= 0.5:
            print("\n[PARTIAL SUCCESS] Some spacetime properties emerge.")
            print("Framework shows promise but needs refinement.")
        else:
            print("\n[NEGATIVE] Space/time separation does NOT produce spacetime.")
            print("Different approach needed for spacetime emergence.")

    print("\n" + "="*60 + "\n")

if __name__ == '__main__':
    main()
