#!/usr/bin/env python3
"""
Mahonian Number Analysis for K(N) = N-2 Derivation

Goal: Find patterns in cumulative Mahonian sums that explain K(N) = N-2

Mahonian number M(n,k) = number of permutations of n elements with exactly k inversions

Our constraint: |V_K| = sum_{i=0}^K M(N,i)
For K = N-2: |V_{N-2}| = sum_{i=0}^{N-2} M(N,i)
"""

import numpy as np
from itertools import permutations
from collections import defaultdict
import matplotlib.pyplot as plt
from math import factorial

def inversion_count(perm):
    """Count inversions in a permutation"""
    inv = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                inv += 1
    return inv

def compute_mahonian_distribution(n):
    """
    Compute Mahonian numbers M(n,k) for all k
    Returns dict: {k: M(n,k)}
    """
    mahonian = defaultdict(int)

    # Generate all permutations and count inversions
    for perm in permutations(range(n)):
        inv = inversion_count(perm)
        mahonian[inv] += 1

    return dict(mahonian)

def cumulative_mahonian(n, K):
    """
    Compute cumulative sum: sum_{i=0}^K M(n,i)
    """
    mahonian = compute_mahonian_distribution(n)
    cumsum = 0
    for i in range(K+1):
        cumsum += mahonian.get(i, 0)
    return cumsum

def analyze_patterns(max_n=8):
    """
    Analyze Mahonian patterns for N=3 through max_n
    """
    print("=" * 80)
    print("MAHONIAN NUMBER ANALYSIS FOR K(N) = N-2")
    print("=" * 80)

    results = {}

    for N in range(3, max_n + 1):
        print(f"\n--- N = {N} ---")

        # Compute Mahonian distribution
        mahonian = compute_mahonian_distribution(N)
        max_inv = N * (N - 1) // 2

        # Print full distribution
        print(f"Mahonian distribution M({N},k):")
        for k in range(max_inv + 1):
            count = mahonian.get(k, 0)
            print(f"  M({N},{k}) = {count}")

        # Verify total
        total = sum(mahonian.values())
        expected = factorial(N)
        match_symbol = 'OK' if total == expected else 'FAIL'
        print(f"Total: {total} (expected {expected}) {match_symbol}")

        # Compute cumulative for K = N-2
        K = N - 2
        cumsum = cumulative_mahonian(N, K)

        print(f"\nCumulative sum for K = {K} (N-2):")
        terms = [mahonian.get(i, 0) for i in range(K+1)]
        print(f"  |V_{K}| = {' + '.join(map(str, terms))} = {cumsum}")

        # Check against known values
        known = {
            3: 3, 4: 9, 5: 29, 6: 98, 7: 343, 8: 1230
        }

        if N in known:
            match = "OK" if cumsum == known[N] else "FAIL"
            print(f"  Expected: {known[N]}, Match: {match}")

        # Store results
        results[N] = {
            'mahonian': mahonian,
            'K': K,
            'cumsum': cumsum,
            'terms': terms
        }

        # Analyze pattern in cumulative terms
        print(f"\nPattern analysis:")
        print(f"  First {K+1} Mahonian numbers: {terms}")

        # Check for arithmetic/geometric patterns
        if len(terms) > 2:
            diffs = [terms[i+1] - terms[i] for i in range(len(terms)-1)]
            print(f"  First differences: {diffs}")

            if len(diffs) > 1:
                second_diffs = [diffs[i+1] - diffs[i] for i in range(len(diffs)-1)]
                print(f"  Second differences: {second_diffs}")

        # Factorization
        print(f"\nFactorization of |V_{K}| = {cumsum}:")
        print(f"  {cumsum} = {factorize(cumsum)}")

    return results

def factorize(n):
    """Return prime factorization as string"""
    if n <= 1:
        return str(n)

    factors = []
    d = 2
    temp = n

    while d * d <= temp:
        while temp % d == 0:
            factors.append(d)
            temp //= d
        d += 1

    if temp > 1:
        factors.append(temp)

    # Group factors
    from collections import Counter
    factor_counts = Counter(factors)

    result = []
    for prime in sorted(factor_counts.keys()):
        count = factor_counts[prime]
        if count == 1:
            result.append(str(prime))
        else:
            result.append(f"{prime}^{count}")

    if not result:
        return "1"

    return " × ".join(result)

def plot_mahonian_patterns(results):
    """
    Create visualizations of Mahonian patterns
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Plot 1: Mahonian distributions
    ax1 = axes[0, 0]
    for N in sorted(results.keys()):
        mahonian = results[N]['mahonian']
        K = results[N]['K']

        k_vals = sorted(mahonian.keys())
        m_vals = [mahonian[k] for k in k_vals]

        # Highlight K=N-2 cutoff
        colors = ['red' if k <= K else 'lightgray' for k in k_vals]

        ax1.scatter([k + 0.1*N for k in k_vals], m_vals,
                   label=f'N={N} (K={K})', alpha=0.7, s=50)

    ax1.set_xlabel('Inversion count k')
    ax1.set_ylabel('M(N,k)')
    ax1.set_title('Mahonian Distributions (red = included in V_K)')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Plot 2: Cumulative sums |V_K|
    ax2 = axes[0, 1]
    N_vals = sorted(results.keys())
    V_K_vals = [results[N]['cumsum'] for N in N_vals]

    ax2.plot(N_vals, V_K_vals, 'bo-', markersize=8, linewidth=2)
    ax2.set_xlabel('N')
    ax2.set_ylabel('|V_{N-2}|')
    ax2.set_title('Valid State Count vs N')
    ax2.grid(True, alpha=0.3)

    # Add annotations for perfect powers
    perfect_powers = {7: '7³', 9: '67²'}
    for N in N_vals:
        if N in perfect_powers:
            ax2.annotate(f'{perfect_powers[N]}',
                        xy=(N, results[N]['cumsum']),
                        xytext=(N+0.3, results[N]['cumsum']*1.1),
                        fontsize=10, color='red',
                        arrowprops=dict(arrowstyle='->', color='red', lw=1))

    # Plot 3: First Mahonian term pattern
    ax3 = axes[1, 0]
    first_terms = []
    for N in sorted(results.keys()):
        K = results[N]['K']
        terms = results[N]['terms']
        first_terms.append(terms)

    for i, N in enumerate(sorted(results.keys())):
        K = results[N]['K']
        terms = results[N]['terms']
        positions = list(range(len(terms)))
        ax3.plot(positions, terms, 'o-', label=f'N={N}', alpha=0.7)

    ax3.set_xlabel('Term index i')
    ax3.set_ylabel('M(N,i)')
    ax3.set_title('First K+1 Mahonian Terms for each N')
    ax3.legend()
    ax3.grid(True, alpha=0.3)

    # Plot 4: Ratio analysis
    ax4 = axes[1, 1]
    for N in sorted(results.keys())[1:]:  # Skip N=3
        terms = results[N]['terms']
        ratios = [terms[i+1]/terms[i] if terms[i] > 0 else 0
                 for i in range(len(terms)-1)]
        ax4.plot(range(len(ratios)), ratios, 'o-', label=f'N={N}', alpha=0.7)

    ax4.set_xlabel('Term index i')
    ax4.set_ylabel('M(N,i+1) / M(N,i)')
    ax4.set_title('Growth Ratios of Mahonian Terms')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    ax4.axhline(y=1, color='k', linestyle='--', alpha=0.3)

    plt.tight_layout()
    plt.savefig('mahonian_patterns.png', dpi=150, bbox_inches='tight')
    print("\nPlot saved as 'mahonian_patterns.png'")
    plt.close()

def search_for_recurrence(results):
    """
    Search for recurrence relation in cumulative sums
    """
    print("\n" + "=" * 80)
    print("RECURRENCE RELATION SEARCH")
    print("=" * 80)

    N_vals = sorted(results.keys())
    V_vals = [results[N]['cumsum'] for N in N_vals]

    print("\nSequence |V_{N-2}|:", V_vals)

    # Test: V_N = a*V_{N-1} + b*V_{N-2} + c
    print("\nTesting linear recurrence V_N = a*V_{N-1} + b*V_{N-2} + c:")

    for i in range(3, len(V_vals)):
        # Solve for a, b, c using three consecutive values
        V_n2, V_n1, V_n = V_vals[i-2], V_vals[i-1], V_vals[i]

        # V_n = a*V_{n-1} + b*V_{n-2} + c
        # System doesn't have unique solution without constraints
        # Try simple cases:

        # Case 1: c=0, find a,b
        # V_n = a*V_{n-1} + b*V_{n-2}
        # We need another equation...

        print(f"  N={N_vals[i]}: V={V_n}, V_{{n-1}}={V_n1}, V_{{n-2}}={V_n2}")

        # Try ratio analysis
        if V_n1 != 0:
            ratio1 = V_n / V_n1
            print(f"    Ratio V_n/V_{{n-1}} = {ratio1:.4f}")

    # Test: V_N related to N!
    print("\nTesting factorial relationship:")
    for N in N_vals:
        V = results[N]['cumsum']
        fact = factorial(N)
        ratio = V / fact
        print(f"  N={N}: |V_{N-2}|/N! = {V}/{fact} = {ratio:.6f}")

    # Test: V_N = polynomial in N?
    print("\nTesting polynomial fit:")
    from numpy.polynomial import Polynomial

    p = Polynomial.fit(N_vals, V_vals, deg=3)
    print(f"  Cubic fit: {p}")

    predictions = [p(N) for N in N_vals]
    errors = [abs(V_vals[i] - predictions[i]) for i in range(len(V_vals))]
    print(f"  Errors: {errors}")
    print(f"  Max error: {max(errors):.2f}")

def analyze_symmetry(results):
    """
    Analyze symmetry in Mahonian distribution
    """
    print("\n" + "=" * 80)
    print("SYMMETRY ANALYSIS")
    print("=" * 80)

    for N in sorted(results.keys()):
        mahonian = results[N]['mahonian']
        max_inv = N * (N - 1) // 2
        K = results[N]['K']

        print(f"\nN={N}, max inversions={max_inv}, K={K}:")

        # Check reflection symmetry: M(n,k) = M(n, max-k)
        symmetric = True
        for k in range(max_inv // 2 + 1):
            m_k = mahonian.get(k, 0)
            m_max_k = mahonian.get(max_inv - k, 0)
            if m_k != m_max_k:
                symmetric = False
                print(f"  Asymmetry: M({N},{k}) = {m_k} ≠ M({N},{max_inv-k}) = {m_max_k}")

        if symmetric:
            print(f"  Distribution is symmetric (OK)")

        # Check if K=N-2 is special relative to symmetry
        complement_K = max_inv - K
        sum_low = results[N]['cumsum']
        sum_high = sum(mahonian.get(i, 0) for i in range(complement_K, max_inv + 1))

        print(f"  Sum for k <= {K}: {sum_low}")
        print(f"  Sum for k >= {complement_K}: {sum_high}")
        print(f"  Complement index: {complement_K} (vs K={K})")

        # Is K approximately at median?
        median_inv = max_inv / 2
        print(f"  Median inversion count: {median_inv:.1f} (K={K})")

if __name__ == "__main__":
    # Main analysis
    results = analyze_patterns(max_n=8)

    # Generate plots
    plot_mahonian_patterns(results)

    # Search for recurrence
    search_for_recurrence(results)

    # Analyze symmetry
    analyze_symmetry(results)

    print("\n" + "=" * 80)
    print("ANALYSIS COMPLETE")
    print("=" * 80)
    print("\nKey findings will be documented in research notes.")
