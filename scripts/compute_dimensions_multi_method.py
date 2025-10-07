"""
Multi-Method Dimension Estimation for Spacetime Scaling

Implements 3 dimension estimators as recommended by expert consultation:
1. Correlation dimension (Grassberger & Procaccia, 1983) - baseline
2. Persistent homology (topological dimension via Betti numbers)
3. Graph-theoretic dimension (spectral + average path length)

Session 4.0 Sprint 9 Phase 2
Expert recommendation: Use multiple methods and compare for robustness

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

# Check for optional libraries
try:
    import ripser
    HAS_RIPSER = True
except ImportError:
    HAS_RIPSER = False
    print("Warning: ripser not installed. Persistent homology will be unavailable.")
    print("Install with: pip install ripser")

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

def extract_time_slice_coords(N, K, h_level):
    """
    Extract coordinates for all permutations at a given h-level.

    Args:
        N: Number of elements
        K: Constraint threshold
        h_level: Time-slice to extract (h-level)

    Returns:
        numpy array of shape (num_states, N-1) with embedding coordinates
    """
    all_perms = list(permutations(range(1, N+1)))
    coords = []

    for perm in all_perms:
        h = compute_inversion_count(perm)
        if h == h_level and h <= K:
            coords.append(permutohedron_embedding(perm))

    return np.array(coords) if coords else np.array([]).reshape(0, N-1)

# ==============================================================================
# Method 1: Correlation Dimension (Baseline)
# ==============================================================================

def estimate_correlation_dimension(coords):
    """
    Estimate dimension using correlation integral method.

    Based on Grassberger & Procaccia (1983).
    C(r) ~ r^d where d = correlation dimension

    Args:
        coords: numpy array of shape (n_points, n_features)

    Returns:
        dict with dimension estimate and diagnostic info
    """
    if len(coords) < 3:
        return {
            'dimension': 0.0,
            'method': 'correlation',
            'status': 'insufficient_data',
            'num_points': len(coords)
        }

    # Compute pairwise distances
    distances = squareform(pdist(coords, metric='euclidean'))

    # Sample radius values
    max_dist = np.max(distances)
    r_values = np.linspace(0.1*max_dist, 0.9*max_dist, 10)

    # Count pairs within each radius
    counts = []
    for r in r_values:
        count = np.sum(distances < r) - len(coords)  # Exclude diagonal
        counts.append(count / 2)  # Each pair counted twice

    # Fit log(count) vs log(r)
    valid = np.array(counts) > 0
    if np.sum(valid) >= 3:
        slope, intercept, r_value, p_value, std_err = linregress(
            np.log(r_values[valid]),
            np.log(np.array(counts)[valid])
        )
        dimension = slope
        fit_quality = r_value**2  # R-squared
    else:
        dimension = 1.0
        fit_quality = 0.0

    return {
        'dimension': dimension,
        'method': 'correlation',
        'fit_quality': fit_quality,
        'num_points': len(coords),
        'status': 'success'
    }

# ==============================================================================
# Method 2: Persistent Homology (Topological)
# ==============================================================================

def estimate_persistent_homology_dimension(coords):
    """
    Estimate dimension using persistent homology (Betti numbers).

    Persistent homology captures topological features at different scales.
    The dimension can be inferred from the persistence diagram.

    Args:
        coords: numpy array of shape (n_points, n_features)

    Returns:
        dict with dimension estimate and Betti numbers
    """
    if not HAS_RIPSER:
        return {
            'dimension': None,
            'method': 'persistent_homology',
            'status': 'library_unavailable',
            'num_points': len(coords)
        }

    if len(coords) < 3:
        return {
            'dimension': 0.0,
            'method': 'persistent_homology',
            'status': 'insufficient_data',
            'num_points': len(coords)
        }

    try:
        # Compute persistence diagram
        result = ripser.ripser(coords, maxdim=min(3, coords.shape[1]))
        diagrams = result['dgms']

        # Analyze Betti numbers at different dimensions
        # Betti_0 = connected components (always 1 for connected space)
        # Betti_1 = 1D holes (loops)
        # Betti_2 = 2D voids
        # Betti_3 = 3D voids

        betti_numbers = []
        for dim, dgm in enumerate(diagrams):
            # Count persistent features (birth-death > threshold)
            if len(dgm) > 0:
                persistence = dgm[:, 1] - dgm[:, 0]
                # Filter out short-lived features (noise)
                threshold = np.percentile(persistence[np.isfinite(persistence)], 50) if len(persistence) > 0 else 0
                significant = np.sum(persistence > threshold)
                betti_numbers.append(significant)
            else:
                betti_numbers.append(0)

        # Estimate dimension from highest non-trivial Betti number
        # For a d-dimensional manifold, expect Betti_d > 0
        dimension = 0
        for i, betti in enumerate(betti_numbers):
            if betti > 0:
                dimension = i

        # Refine estimate: if we have features in multiple dimensions
        # use weighted average
        if sum(betti_numbers) > 0:
            weights = np.array(betti_numbers) / sum(betti_numbers)
            dimension = sum(i * w for i, w in enumerate(weights))

        return {
            'dimension': float(dimension),
            'method': 'persistent_homology',
            'betti_numbers': betti_numbers,
            'num_points': len(coords),
            'status': 'success'
        }

    except Exception as e:
        return {
            'dimension': None,
            'method': 'persistent_homology',
            'status': 'error',
            'error': str(e),
            'num_points': len(coords)
        }

# ==============================================================================
# Method 3: Graph-Theoretic Dimension
# ==============================================================================

def estimate_graph_theoretic_dimension(coords):
    """
    Estimate dimension using graph-theoretic properties.

    Two approaches:
    1. Spectral dimension from graph Laplacian eigenvalues
    2. Average path length scaling

    Args:
        coords: numpy array of shape (n_points, n_features)

    Returns:
        dict with dimension estimates from both methods
    """
    if len(coords) < 3:
        return {
            'dimension': 0.0,
            'method': 'graph_theoretic',
            'status': 'insufficient_data',
            'num_points': len(coords)
        }

    # Build graph (k-nearest neighbors)
    k = min(5, len(coords) - 1)  # Connect to 5 nearest neighbors
    distances = squareform(pdist(coords, metric='euclidean'))

    G = nx.Graph()
    for i in range(len(coords)):
        G.add_node(i)

    # Add edges to k nearest neighbors
    for i in range(len(coords)):
        nearest = np.argsort(distances[i])[1:k+1]  # Skip self (index 0)
        for j in nearest:
            G.add_edge(i, j, weight=distances[i, j])

    # Method 3a: Spectral dimension
    try:
        laplacian = nx.laplacian_matrix(G).todense()
        eigenvalues = np.linalg.eigvalsh(laplacian)

        # Spectral dimension from eigenvalue density
        # d_s ≈ 2 * sum(λ_i) / sum(λ_i^2)
        eigenvalues = eigenvalues[eigenvalues > 1e-10]  # Filter near-zero
        if len(eigenvalues) > 0:
            spectral_dim = 2 * np.sum(eigenvalues) / np.sum(eigenvalues**2)
        else:
            spectral_dim = 1.0
    except:
        spectral_dim = None

    # Method 3b: Average path length scaling
    try:
        if nx.is_connected(G):
            avg_path_length = nx.average_shortest_path_length(G)
            # For d-dimensional lattice: <l> ~ N^(1/d)
            # So d ≈ log(N) / log(<l>)
            if avg_path_length > 1:
                path_dim = np.log(len(coords)) / np.log(avg_path_length)
            else:
                path_dim = 1.0
        else:
            path_dim = None
    except:
        path_dim = None

    # Combine estimates
    estimates = [x for x in [spectral_dim, path_dim] if x is not None]
    if estimates:
        dimension = np.mean(estimates)
    else:
        dimension = 1.0

    return {
        'dimension': dimension,
        'method': 'graph_theoretic',
        'spectral_dimension': spectral_dim,
        'path_length_dimension': path_dim,
        'num_points': len(coords),
        'graph_connected': nx.is_connected(G),
        'status': 'success'
    }

# ==============================================================================
# Multi-Method Analysis
# ==============================================================================

def analyze_dimension_multi_method(N, K, h_level):
    """
    Compute dimension using all three methods and compare.

    Args:
        N: Number of elements
        K: Constraint threshold
        h_level: Time-slice to analyze

    Returns:
        dict with results from all methods
    """
    print(f"  Analyzing N={N}, K={K}, h={h_level}...")

    # Extract coordinates
    coords = extract_time_slice_coords(N, K, h_level)

    if len(coords) == 0:
        print(f"    No states at h={h_level}")
        return None

    print(f"    Found {len(coords)} states")

    # Run all three methods
    results = {
        'N': N,
        'K': K,
        'h': h_level,
        'num_states': len(coords)
    }

    # Method 1: Correlation dimension
    corr_result = estimate_correlation_dimension(coords)
    results['correlation'] = corr_result
    if corr_result['status'] == 'success':
        print(f"    Correlation dimension: {corr_result['dimension']:.2f}")

    # Method 2: Persistent homology
    ph_result = estimate_persistent_homology_dimension(coords)
    results['persistent_homology'] = ph_result
    if ph_result['status'] == 'success':
        print(f"    Persistent homology dimension: {ph_result['dimension']:.2f}")
        print(f"      Betti numbers: {ph_result['betti_numbers']}")
    elif ph_result['status'] == 'library_unavailable':
        print(f"    Persistent homology: UNAVAILABLE (ripser not installed)")

    # Method 3: Graph-theoretic
    graph_result = estimate_graph_theoretic_dimension(coords)
    results['graph_theoretic'] = graph_result
    if graph_result['status'] == 'success':
        print(f"    Graph-theoretic dimension: {graph_result['dimension']:.2f}")
        if graph_result['spectral_dimension'] is not None:
            print(f"      Spectral: {graph_result['spectral_dimension']:.2f}")
        if graph_result['path_length_dimension'] is not None:
            print(f"      Path length: {graph_result['path_length_dimension']:.2f}")

    # Compute consensus estimate
    dimensions = []
    if corr_result['status'] == 'success':
        dimensions.append(corr_result['dimension'])
    if ph_result['status'] == 'success':
        dimensions.append(ph_result['dimension'])
    if graph_result['status'] == 'success':
        dimensions.append(graph_result['dimension'])

    if dimensions:
        results['consensus_dimension'] = np.mean(dimensions)
        results['dimension_std'] = np.std(dimensions) if len(dimensions) > 1 else 0.0
        print(f"    Consensus dimension: {results['consensus_dimension']:.2f} ± {results['dimension_std']:.2f}")
    else:
        results['consensus_dimension'] = None
        results['dimension_std'] = None

    return results

def main():
    """
    Run multi-method dimension analysis for N=3,4,5,6,7
    """
    print("=" * 70)
    print("MULTI-METHOD DIMENSION ESTIMATION")
    print("=" * 70)
    print()
    print("Methods:")
    print("  1. Correlation dimension (Grassberger & Procaccia)")
    print("  2. Persistent homology (Betti numbers)")
    print("  3. Graph-theoretic (spectral + path length)")
    print()

    # Test cases (N, K, h_level to analyze)
    test_cases = [
        (3, 1, 1),  # N=3, K=1, max h=1
        (4, 2, 2),  # N=4, K=2, max h=2
        (5, 3, 3),  # N=5, K=3, max h=3
        (6, 4, 4),  # N=6, K=4, max h=4
        (7, 5, 5),  # N=7, K=5, max h=5
        (8, 6, 6),  # N=8, K=6, max h=6 (Phase 3)
    ]

    all_results = []

    for N, K, h_level in test_cases:
        result = analyze_dimension_multi_method(N, K, h_level)
        if result is not None:
            all_results.append(result)
        print()

    # Save results
    output_dir = 'C:/Users/jdlon/OneDrive/Documents/physical_logic_framework/paper/supporting_material/spacetime_research'
    output_file = f'{output_dir}/multi_method_dimensions.json'

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

    serializable_results = {
        'results': convert_to_serializable(all_results),
        'metadata': {
            'date': datetime.now().isoformat(),
            'methods': ['correlation', 'persistent_homology', 'graph_theoretic'],
            'test_version': 'Sprint 9 Phase 2'
        }
    }

    with open(output_file, 'w') as f:
        json.dump(serializable_results, f, indent=2)

    print(f"[OK] Results saved to {output_file}")

    # Print summary table
    print()
    print("=" * 70)
    print("DIMENSION SUMMARY")
    print("=" * 70)
    print()
    print(f"{'N':>3} {'K':>3} {'h':>3} {'States':>7} {'Corr':>6} {'PH':>6} {'Graph':>6} {'Consensus':>10}")
    print("-" * 70)

    for result in all_results:
        N = result['N']
        K = result['K']
        h = result['h']
        states = result['num_states']

        corr = result['correlation']['dimension'] if result['correlation']['status'] == 'success' else None
        ph = result['persistent_homology']['dimension'] if result['persistent_homology']['status'] == 'success' else None
        graph = result['graph_theoretic']['dimension'] if result['graph_theoretic']['status'] == 'success' else None
        consensus = result.get('consensus_dimension')
        std = result.get('dimension_std', 0.0)

        corr_str = f"{corr:.2f}" if corr is not None else "N/A"
        ph_str = f"{ph:.2f}" if ph is not None else "N/A"
        graph_str = f"{graph:.2f}" if graph is not None else "N/A"
        consensus_str = f"{consensus:.2f}±{std:.2f}" if consensus is not None else "N/A"

        print(f"{N:>3} {K:>3} {h:>3} {states:>7} {corr_str:>6} {ph_str:>6} {graph_str:>6} {consensus_str:>10}")

    print()
    print("=" * 70)
    print()

if __name__ == '__main__':
    main()
