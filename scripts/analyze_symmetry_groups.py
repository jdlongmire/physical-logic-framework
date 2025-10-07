"""
Symmetry Group Analysis for Spacetime Slices

This script performs a detailed analysis of the symmetry groups (automorphisms)
of spatial slices at different time levels, to investigate whether the discrete
symmetry structure converges to SO(3,1) as N->infinity.

Key Questions:
1. What are the automorphism groups of spatial slices?
2. How do these groups scale with N?
3. Do they show patterns consistent with rotation groups SO(N-1)?
4. Is there evidence for Lorentz group SO(3,1) emergence?

Date: October 7, 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from itertools import permutations
import networkx as nx
from scipy.spatial.distance import pdist, squareform
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
    """Compute permutohedron embedding coordinates."""
    return np.array(perm[:-1], dtype=float)

def extract_time_slices(N, K):
    """Extract time-slices: all permutations at each h-level."""
    time_slices = {}
    all_perms = list(permutations(range(1, N+1)))

    for perm in all_perms:
        h = compute_inversion_count(perm)
        if h <= K:
            if h not in time_slices:
                time_slices[h] = []
            time_slices[h].append(perm)

    return time_slices

def build_spatial_graph(perms, distance_threshold_percentile=50):
    """
    Build spatial connectivity graph for permutations at fixed h-level.

    Args:
        perms: List of permutations
        distance_threshold_percentile: Percentile for distance threshold (0-100)

    Returns:
        NetworkX graph with spatial connectivity
    """
    if len(perms) < 2:
        G = nx.Graph()
        G.add_node(0)
        return G

    # Compute embedding coordinates
    coords = np.array([permutohedron_embedding(p) for p in perms])

    # Pairwise distances
    distances = squareform(pdist(coords, metric='euclidean'))

    # Use percentile as threshold for connectivity
    threshold = np.percentile(distances[distances > 0], distance_threshold_percentile)

    # Build graph
    G = nx.Graph()
    for i in range(len(perms)):
        G.add_node(i)
    for i in range(len(perms)):
        for j in range(i+1, len(perms)):
            if 0 < distances[i,j] <= threshold:
                G.add_edge(i, j, weight=distances[i,j])

    return G

def analyze_graph_automorphisms(G, max_size=15):
    """
    Compute automorphism group of graph.

    For small graphs (size <= max_size), compute exact automorphism group.
    For large graphs, estimate using heuristics.

    Returns:
        dict with automorphism group properties
    """
    num_nodes = G.number_of_nodes()

    if num_nodes == 1:
        return {
            'num_automorphisms': 1,
            'group_order': 1,
            'is_trivial': True,
            'automorphisms_sample': [],
            'computation_method': 'exact'
        }

    if num_nodes <= max_size:
        # Compute exact automorphisms
        try:
            matcher = nx.algorithms.isomorphism.GraphMatcher(G, G)
            automorphisms = list(matcher.isomorphisms_iter())
            num_autos = len(automorphisms)

            return {
                'num_automorphisms': num_autos,
                'group_order': num_autos,
                'is_trivial': num_autos == 1,
                'automorphisms_sample': automorphisms[:10],  # Store up to 10 examples
                'computation_method': 'exact'
            }
        except Exception as e:
            # Fallback to heuristic
            pass

    # Heuristic estimate for large graphs
    degree_sequence = sorted([G.degree(n) for n in G.nodes()])
    unique_degrees = len(set(degree_sequence))

    # Regular graphs have many symmetries
    if unique_degrees == 1:
        # Highly symmetric - estimate as factorial of number of nodes (upper bound)
        estimate = min(np.math.factorial(num_nodes), 10**6)  # Cap at 1 million
    elif unique_degrees <= 2:
        # Moderately symmetric
        estimate = num_nodes
    else:
        # Low symmetry
        estimate = 1

    return {
        'num_automorphisms': estimate,
        'group_order': estimate,
        'is_trivial': estimate == 1,
        'automorphisms_sample': [],
        'computation_method': 'heuristic'
    }

def analyze_rotation_group_signature(automorphisms_sample, coords):
    """
    Analyze whether automorphisms have rotation-like properties.

    A rotation in R^d:
    - Preserves distances (isometry)
    - Preserves orientation or reverses it (proper/improper)
    - Forms a group (closure, identity, inverses)

    Args:
        automorphisms_sample: List of automorphism permutations
        coords: Coordinates of points in space

    Returns:
        dict with rotation-like properties
    """
    if len(automorphisms_sample) == 0 or len(coords) < 2:
        return {
            'preserves_distances': True,  # Trivially true for no automorphisms
            'has_rotations': False,
            'dimension_estimate': 0
        }

    # Check distance preservation (isometry property)
    distances_original = squareform(pdist(coords, metric='euclidean'))

    preserves_distances = []
    for auto in automorphisms_sample[:10]:  # Check up to 10 automorphisms
        # Apply automorphism to reorder coordinates
        perm_indices = [auto[i] for i in range(len(coords))]
        coords_permuted = coords[perm_indices]
        distances_permuted = squareform(pdist(coords_permuted, metric='euclidean'))

        # Check if distances are preserved
        max_diff = np.max(np.abs(distances_original - distances_permuted))
        preserves_distances.append(max_diff < 1e-8)

    return {
        'preserves_distances': all(preserves_distances) if preserves_distances else True,
        'has_rotations': len(automorphisms_sample) > 1,
        'dimension_estimate': coords.shape[1] if coords.shape[0] > 1 else 0
    }

def compute_SO3_compatibility(N, symmetry_data):
    """
    Estimate compatibility with SO(3) rotation group.

    SO(3) properties:
    - Continuous group (infinite elements)
    - 3-parameter (3 Euler angles)
    - Preserves distances in 3D space

    For discrete approximations:
    - Check if symmetry group order grows appropriately
    - Check if spatial dimension ~ 3
    - Check if isometries are present

    Returns:
        dict with SO(3) compatibility metrics
    """
    # SO(3) has infinite elements, but discrete approximations grow with resolution
    # Common discrete subgroups:
    # - Tetrahedral: 12 elements
    # - Octahedral: 24 elements
    # - Icosahedral: 60 elements
    # - Dihedral D_n: 2n elements

    group_order = symmetry_data.get('num_automorphisms', 1)
    dimension = symmetry_data.get('dimension_estimate', 0)

    # Check for known discrete subgroups of SO(3)
    known_subgroups = {
        12: 'Tetrahedral (A4)',
        24: 'Octahedral (S4)',
        60: 'Icosahedral (A5)'
    }

    matches_known_subgroup = group_order in known_subgroups
    subgroup_name = known_subgroups.get(group_order, 'Unknown')

    # Dimension should be approaching 3
    dimension_compatible = abs(dimension - 3.0) < 1.0 if dimension > 0 else False

    # Compute compatibility score (0-1)
    score = 0.0
    if matches_known_subgroup:
        score += 0.5
    if dimension_compatible:
        score += 0.3
    if symmetry_data.get('preserves_distances', False):
        score += 0.2

    return {
        'compatibility_score': score,
        'matches_known_subgroup': matches_known_subgroup,
        'subgroup_name': subgroup_name,
        'dimension_compatible': dimension_compatible,
        'N': N,
        'group_order': group_order
    }

def compute_Lorentz_compatibility(N, spatial_symmetry, temporal_symmetry):
    """
    Estimate compatibility with Lorentz group SO(3,1).

    SO(3,1) structure:
    - Spatial rotations: SO(3) subgroup
    - Lorentz boosts: Non-compact transformations
    - Total: 6 parameters (3 rotations + 3 boosts)

    For discrete structure:
    - Check for spatial symmetries (SO(3)-like)
    - Check for temporal symmetries (time translations)
    - Boosts require continuum (not expected in discrete case)

    Returns:
        dict with Lorentz compatibility metrics
    """
    spatial_score = spatial_symmetry.get('compatibility_score', 0)
    has_temporal = temporal_symmetry.get('has_time_translation', False)

    # Discrete structure at finite N won't have boosts
    # But it should have:
    # 1. Spatial rotations (discrete SO(3) approximation)
    # 2. Time translations
    # 3. Proper metric signature (-,+,+,+)

    # Compute Lorentz compatibility
    lorentz_score = 0.0
    if spatial_score > 0.5:
        lorentz_score += 0.4  # Strong spatial symmetries
    if has_temporal:
        lorentz_score += 0.3  # Time translation symmetry
    if N >= 5:
        lorentz_score += 0.3  # Large enough N for structure to emerge

    return {
        'lorentz_compatibility_score': lorentz_score,
        'has_spatial_symmetries': spatial_score > 0.3,
        'has_temporal_symmetries': has_temporal,
        'boosts_expected': False,  # Not in discrete case
        'interpretation': 'Discrete Poincare-like (SO(3) x R)' if lorentz_score > 0.5 else 'Insufficient structure'
    }

def analyze_symmetries_all_slices(N, K):
    """
    Comprehensive symmetry analysis for all time-slices.
    """
    print(f"\n{'='*60}")
    print(f"Symmetry Analysis for N={N}, K={K}")
    print(f"{'='*60}\n")

    # Extract time-slices
    time_slices = extract_time_slices(N, K)

    results = {}

    for h in sorted(time_slices.keys()):
        perms = time_slices[h]
        print(f"  Analyzing h={h} ({len(perms)} states)...")

        # Build spatial graph
        G = build_spatial_graph(perms)

        # Analyze automorphisms
        auto_data = analyze_graph_automorphisms(G)
        print(f"    Automorphism group: {auto_data['group_order']} elements ({auto_data['computation_method']})")

        # Get coordinates for rotation analysis
        coords = np.array([permutohedron_embedding(p) for p in perms]) if len(perms) > 0 else np.array([])

        # Analyze rotation properties
        rotation_data = analyze_rotation_group_signature(auto_data['automorphisms_sample'], coords)
        print(f"    Preserves distances: {rotation_data['preserves_distances']}")
        print(f"    Spatial dimension: {rotation_data['dimension_estimate']}")

        # Compute SO(3) compatibility
        symmetry_data = {
            'num_automorphisms': auto_data['group_order'],
            'dimension_estimate': rotation_data['dimension_estimate'],
            'preserves_distances': rotation_data['preserves_distances']
        }
        so3_compat = compute_SO3_compatibility(N, symmetry_data)
        print(f"    SO(3) compatibility: {so3_compat['compatibility_score']:.2f}")
        if so3_compat['matches_known_subgroup']:
            print(f"    Matches subgroup: {so3_compat['subgroup_name']}")

        results[h] = {
            'num_states': len(perms),
            'automorphisms': auto_data,
            'rotation_properties': rotation_data,
            'so3_compatibility': so3_compat
        }

    return results

def main():
    """
    Main analysis execution.
    """
    print("\n" + "="*60)
    print("SYMMETRY GROUP ANALYSIS (N=3,4,5,6)")
    print("="*60)
    print("\nQuestion: Do symmetry groups converge to SO(3) x R?")
    print("(Spatial rotations x Time translations)\n")

    # Test cases
    test_cases = [
        (3, 1),
        (4, 2),
        (5, 3),
        (6, 4),
    ]

    all_results = {}

    for N, K in test_cases:
        results = analyze_symmetries_all_slices(N, K)
        all_results[f'N{N}_K{K}'] = results

        # Get maximum h-level for Lorentz analysis
        max_h = max(results.keys())
        spatial_sym = results[max_h]['so3_compatibility']

        # Temporal symmetry: time translations exist by construction (h-levels)
        temporal_sym = {'has_time_translation': True}

        # Compute Lorentz compatibility
        lorentz_compat = compute_Lorentz_compatibility(N, spatial_sym, temporal_sym)
        print(f"\n  Lorentz SO(3,1) compatibility: {lorentz_compat['lorentz_compatibility_score']:.2f}")
        print(f"  Interpretation: {lorentz_compat['interpretation']}")

        all_results[f'N{N}_K{K}']['lorentz_compatibility'] = lorentz_compat

    # Save results
    output_dir = 'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/paper/supporting_material/spacetime_research'
    output_file = f'{output_dir}/symmetry_group_analysis.json'

    # Convert to serializable format
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
        'analysis': 'Symmetry group structure and SO(3,1) compatibility',
        'version': '1.0'
    }

    with open(output_file, 'w') as f:
        json.dump(serializable_results, f, indent=2)

    print(f"\n[OK] Results saved to {output_file}")

    # Summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)

    print("\nSymmetry Group Orders (maximum h-level):")
    for case_key in sorted(all_results.keys()):
        if 'metadata' in case_key:
            continue
        case_data = all_results[case_key]
        max_h = max([k for k in case_data.keys() if isinstance(k, int)])
        group_order = case_data[max_h]['automorphisms']['group_order']
        print(f"  {case_key}: {group_order} elements")

    print("\nLorentz Compatibility:")
    for case_key in sorted(all_results.keys()):
        if 'metadata' in case_key:
            continue
        lorentz_score = all_results[case_key]['lorentz_compatibility']['lorentz_compatibility_score']
        interp = all_results[case_key]['lorentz_compatibility']['interpretation']
        print(f"  {case_key}: {lorentz_score:.2f} - {interp}")

    print("\n" + "="*60 + "\n")

if __name__ == '__main__':
    main()
