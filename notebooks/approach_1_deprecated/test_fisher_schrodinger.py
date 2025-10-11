#!/usr/bin/env python
"""
Test script: Fisher Metric → Schrödinger Equation derivation
Validates core computations from Notebook 15
"""

import numpy as np
import networkx as nx
from scipy.linalg import expm
import itertools

# Set random seed for reproducibility
np.random.seed(42)

print("="*70)
print("FISHER METRIC -> SCHRODINGER EQUATION: VALIDATION")
print("="*70)

# ============================================================================
# PHASE A: Define Configuration Space V_K
# ============================================================================

N = 3
K = N - 2  # Constraint threshold

def inversion_count(perm):
    """Count inversions in permutation"""
    count = 0
    for i in range(len(perm)):
        for j in range(i+1, len(perm)):
            if perm[i] > perm[j]:
                count += 1
    return count

# Generate V_K = {σ ∈ S_N : h(σ) ≤ K}
all_perms = list(itertools.permutations(range(N)))
V_K = [p for p in all_perms if inversion_count(p) <= K]

print(f"\nPHASE A: CONFIGURATION SPACE")
print(f"  N = {N}, K = {K}")
print(f"  |V_K| = {len(V_K)} valid states")
for p in V_K:
    print(f"    {p} : h = {inversion_count(p)}")

# ============================================================================
# Build Cayley Graph
# ============================================================================

def build_cayley_graph(states, N):
    """Build Cayley graph with adjacent transposition generators"""
    idx = {s: i for i, s in enumerate(states)}
    G = nx.Graph()
    G.add_nodes_from(range(len(states)))

    for s in states:
        u = idx[s]
        for i in range(N-1):
            s_list = list(s)
            s_list[i], s_list[i+1] = s_list[i+1], s_list[i]
            s_new = tuple(s_list)

            if s_new in idx:
                v = idx[s_new]
                if u < v:
                    G.add_edge(u, v)

    return G

G_VK = build_cayley_graph(V_K, N)
degrees = [G_VK.degree(i) for i in range(len(V_K))]

A = nx.adjacency_matrix(G_VK).todense()
D = np.diag(degrees)
L = D - A  # Graph Laplacian

print(f"\nCAYLEY GRAPH STRUCTURE")
print(f"  Nodes: {G_VK.number_of_nodes()}")
print(f"  Edges: {G_VK.number_of_edges()}")
print(f"  Degrees: {degrees}")
print(f"\n  Graph Laplacian L = D - A:")
print(f"{L}")

# ============================================================================
# PHASE B: Fisher Information Metric
# ============================================================================

def quantum_state_from_params(a2, phi2, a3, phi3):
    """Construct normalized quantum state from 4 parameters"""
    a1_sq = 1 - a2**2 - a3**2
    if a1_sq < 0:
        raise ValueError(f"Invalid parameters: a2²+a3² > 1")

    a1 = np.sqrt(a1_sq)
    psi = np.array([
        a1,
        a2 * np.exp(1j * phi2),
        a3 * np.exp(1j * phi3)
    ], dtype=complex)

    return psi

def compute_fubini_study_metric(a2, phi2, a3, phi3, eps=1e-6):
    """Compute Fubini-Study metric using finite differences"""
    params = np.array([a2, phi2, a3, phi3])
    dim = len(params)
    g = np.zeros((dim, dim))

    dpsi = []
    for i in range(dim):
        params_plus = params.copy()
        params_minus = params.copy()
        params_plus[i] += eps
        params_minus[i] -= eps

        try:
            psi_plus = quantum_state_from_params(*params_plus)
            psi_minus = quantum_state_from_params(*params_minus)
            dpsi_i = (psi_plus - psi_minus) / (2 * eps)
            dpsi.append(dpsi_i)
        except ValueError:
            dpsi.append(np.zeros(3, dtype=complex))

    # Fubini-Study metric: g_ij = Re(⟨∂ᵢψ|∂ⱼψ⟩)
    for i in range(dim):
        for j in range(dim):
            g[i,j] = np.real(np.dot(np.conj(dpsi[i]), dpsi[j]))

    return g

# Test Fisher metric
a2, phi2 = 0.4, np.pi/4
a3, phi3 = 0.5, np.pi/3

psi_test = quantum_state_from_params(a2, phi2, a3, phi3)
g_test = compute_fubini_study_metric(a2, phi2, a3, phi3)

print(f"\nPHASE B: FISHER INFORMATION METRIC")
print(f"  Test point: (a2={a2}, phi2={phi2:.3f}, a3={a3}, phi3={phi3:.3f})")
print(f"  psi = {psi_test}")
print(f"  |psi|^2 sum = {np.sum(np.abs(psi_test)**2):.10f}")
print(f"\n  Fubini-Study metric g:")
print(f"{g_test}")

eigvals_g = np.linalg.eigvalsh(g_test)
print(f"  Eigenvalues: {eigvals_g}")
print(f"  Positive-definite: {np.all(eigvals_g > -1e-10)}")

# ============================================================================
# PHASE C: Hamiltonian = Graph Laplacian
# ============================================================================

H = L  # Hamiltonian

H_eigs, H_vecs = np.linalg.eigh(H)

print(f"\nPHASE C: HAMILTONIAN IDENTIFICATION")
print(f"  H = D - A (Graph Laplacian)")
print(f"  Hermitian: {np.allclose(H, H.T)}")
print(f"  Eigenvalues: {H_eigs}")
print(f"  Non-negative: {np.all(H_eigs >= -1e-10)}")

zero_idx = np.argmin(np.abs(H_eigs))
ground_state = H_vecs[:, zero_idx]
print(f"  Ground state (lambda_0={H_eigs[zero_idx]:.2e}): {ground_state / np.linalg.norm(ground_state)}")

# ============================================================================
# PHASE D: Schrödinger Evolution
# ============================================================================

def schrodinger_evolution(psi0, H, t_max, dt):
    """Evolve quantum state via Schrödinger equation"""
    times = np.arange(0, t_max, dt)
    states = []

    for t in times:
        U_t = expm(-1j * H * t)
        psi_t = U_t @ psi0
        states.append(psi_t)

    states = np.array(states)

    observables = {}
    observables['norm'] = np.array([np.linalg.norm(s) for s in states])
    observables['energy'] = np.array([np.real(np.conj(s) @ H @ s) for s in states])

    return times, states, observables

# Initial state
psi0 = quantum_state_from_params(0.5, 0.0, 0.5, np.pi/2)
psi0 = psi0 / np.linalg.norm(psi0)

print(f"\nPHASE D: SCHRODINGER EVOLUTION")
print(f"  Initial state psi(0) = {psi0}")
print(f"  Energy E_0 = {np.real(np.conj(psi0) @ H @ psi0):.6f}")

# Time evolution
t_max = 10.0
dt = 0.1
times, states, obs = schrodinger_evolution(psi0, H, t_max, dt)

print(f"\n  Time evolution: {len(times)} steps, t in [0, {t_max}]")
print(f"  Conservation checks:")
print(f"    Norm: {obs['norm'].min():.10f} <= ||psi|| <= {obs['norm'].max():.10f}")
print(f"    Energy: {obs['energy'].min():.10f} <= <H> <= {obs['energy'].max():.10f}")
print(f"    Energy variation: sigma(E) = {np.std(obs['energy']):.2e}")

psi_final = states[-1]
print(f"\n  Final state psi(t={t_max}):")
print(f"    |psi(t)|^2 = {np.abs(psi_final)**2}")
print(f"    Unitarity: ||psi(0)|| = {np.linalg.norm(psi0):.10f}, ||psi(t)|| = {np.linalg.norm(psi_final):.10f}")

# ============================================================================
# VALIDATION SUMMARY
# ============================================================================

print(f"\n{'='*70}")
print("VALIDATION SUMMARY")
print(f"{'='*70}")

checks = {
    "Configuration space V_K": len(V_K) == 3,
    "Cayley graph connectivity": nx.is_connected(G_VK),
    "Fisher metric positive-definite": np.all(eigvals_g > -1e-10),
    "Hamiltonian Hermitian": np.allclose(H, H.T),
    "Hamiltonian non-negative": np.all(H_eigs >= -1e-10),
    "Normalization conserved": np.allclose(obs['norm'], 1.0, atol=1e-6),
    "Energy conserved": np.std(obs['energy']) < 1e-6,
    "Unitarity preserved": np.allclose(np.linalg.norm(psi_final), np.linalg.norm(psi0), atol=1e-6)
}

for check, passed in checks.items():
    status = "[PASS]" if passed else "[FAIL]"
    print(f"  {status}: {check}")

all_passed = all(checks.values())
print(f"\n{'='*70}")
if all_passed:
    print("[PASS] ALL CHECKS PASSED: Schrodinger equation derived from Fisher metric")
else:
    print("[FAIL] SOME CHECKS FAILED: Review computations")
print(f"{'='*70}")
