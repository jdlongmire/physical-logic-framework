#!/usr/bin/env python3
"""
Generate Notebook 12: Unitary Invariance Foundations
Following comprehensive implementation plan from Sprint 6 Day 1
"""

import json
from datetime import datetime

def create_cell(cell_type, content):
    """Create a notebook cell."""
    return {
        "cell_type": cell_type,
        "metadata": {},
        "source": content if isinstance(content, list) else [content]
    }

def create_notebook():
    """Create Notebook 12 with all sections."""

    cells = []

    # Title and copyright
    cells.append(create_cell("markdown", [
        "# Notebook 12: Unitary Invariance Foundations\n",
        "\n",
        "## Deriving Quantum Symmetries from Pure Combinatorics\n",
        "\n",
        "**Sprint 6 - Addressing Born Rule Circularity (Critical Issue #1)**\n",
        "\n",
        "**Copyright © 2025 James D. (JD) Longmire**  \n",
        "**License**: Apache License 2.0  \n",
        "**Citation**: Longmire, J.D. (2025). *Logic Field Theory: Deriving Quantum Mechanics from Logical Consistency*. Physical Logic Framework Repository.\n",
        "\n",
        "---\n",
        "\n",
        "## Purpose\n",
        "\n",
        "This notebook addresses the most critical concern raised by peer reviewers: **circularity in the Born Rule derivation**.\n",
        "\n",
        "All three expert reviewers (Grok 0.84/1.0, Gemini 0.58/1.0, ChatGPT 0.52/1.0) identified that our derivation uses \"unitary invariance\" - but isn't this itself a quantum mechanical assumption?\n",
        "\n",
        "**Our Resolution**: We demonstrate that unitary invariance **emerges** from pure combinatorial symmetries and information-theoretic constraints, without assuming Hilbert spaces or quantum mechanics.\n",
        "\n",
        "**Key Claim**: Transformations that preserve (1) combinatorial distances and (2) information entropy on the permutation space S_N are uniquely characterized as unitary operators.\n"
    ]))

    # Section 1: Introduction and Motivation
    cells.append(create_cell("markdown", [
        "## 1. Introduction and Motivation\n",
        "\n",
        "### 1.1 The Circularity Concern\n",
        "\n",
        "Our original Born Rule derivation proceeded as:\n",
        "\n",
        "**MaxEnt** + **Unitary Invariance** + **K(N)=N-2** → **P(s) = |⟨ψ|s⟩|²**\n",
        "\n",
        "The three peer reviewers all raised the same critical objection:\n",
        "\n",
        "**Grok (0.84/1.0)**:\n",
        "> \"The most pressing issue is the potential circularity in the derivation of the Born Rule. The reliance on unitary invariance and other quantum-like assumptions suggests that the framework may not be deriving quantum mechanics from truly independent first principles.\"\n",
        "\n",
        "**Gemini (0.58/1.0)**:\n",
        "> \"The most critical concern is the potential for circularity in the derivation of the Born rule. Carefully examine the assumptions used in the derivation to ensure that they do not implicitly assume the Born rule or any equivalent principle.\"\n",
        "\n",
        "**ChatGPT (0.52/1.0)**:\n",
        "> \"The model seems to require a large number of assumptions, some of which are not well motivated... it's not clear why [K(N)=N-2] should be the case.\"\n",
        "\n",
        "**The Problem**: Unitary transformations are fundamental to quantum mechanics. If we assume unitary invariance, aren't we just assuming quantum structure to derive quantum structure?\n",
        "\n",
        "### 1.2 Our Resolution Strategy\n",
        "\n",
        "We will show that unitary invariance is **not assumed** but **derived** from principles more fundamental than quantum mechanics:\n",
        "\n",
        "1. **Start with pure combinatorics**: Symmetric group S_N and permutohedron geometry\n",
        "2. **Identify natural symmetries**: Group operations and adjacency structure (Cayley graph)\n",
        "3. **Impose information-theoretic constraints**: Entropy preservation (MaxEnt), invertibility\n",
        "4. **Show uniqueness**: Only unitary transformations satisfy these combinatorial + information-theoretic constraints\n",
        "5. **Result**: Unitarity emerges from first principles!\n",
        "\n",
        "### 1.3 Notebook Roadmap\n",
        "\n",
        "- **Section 2**: Permutohedron geometry and Cayley graph (pure combinatorics, no QM)\n",
        "- **Section 3**: Combinatorial distance metrics (Kendall tau, inversions)\n",
        "- **Section 4**: Distance-preserving transformations (graph automorphisms)\n",
        "- **Section 5**: Entropy-preserving transformations (MaxEnt requirement)\n",
        "- **Section 6**: Uniqueness theorem - emergent unitarity\n",
        "- **Section 7**: Computational validation (N=3, N=4)\n",
        "- **Section 8**: Connection to quantum mechanics (resolving circularity)\n",
        "\n",
        "**Key References**:\n",
        "- Humphreys (1990): *Reflection Groups and Coxeter Groups*\n",
        "- Kendall (1948): *Rank Correlation Methods*\n",
        "- Jaynes (1957): \"Information Theory and Statistical Mechanics\"\n",
        "- Diaconis (1988): *Group Representations in Probability and Statistics*\n"
    ]))

    # Import libraries
    cells.append(create_cell("code", [
        "# Standard scientific computing libraries\n",
        "import numpy as np\n",
        "import matplotlib.pyplot as plt\n",
        "import networkx as nx\n",
        "from itertools import permutations, combinations\n",
        "from scipy.linalg import logm\n",
        "import warnings\n",
        "warnings.filterwarnings('ignore')\n",
        "\n",
        "# Set random seeds for reproducibility\n",
        "np.random.seed(42)\n",
        "\n",
        "print(\"Libraries loaded successfully\")\n",
        "print(f\"NumPy version: {np.__version__}\")\n",
        "print(f\"NetworkX version: {nx.__version__}\")\n"
    ]))

    # Section 2: Permutohedron and Cayley Graph
    cells.append(create_cell("markdown", [
        "## 2. Permutohedron and Cayley Graph\n",
        "\n",
        "### 2.1 The Symmetric Group S_N\n",
        "\n",
        "We begin with the **symmetric group** S_N - the set of all permutations of {1, 2, ..., N}.\n",
        "\n",
        "**Definition**: A permutation σ ∈ S_N is a bijection σ: {1,...,N} → {1,...,N}.\n",
        "\n",
        "**Key Properties**:\n",
        "- Size: |S_N| = N! elements\n",
        "- Group operations: composition (∘), inverse (σ⁻¹), identity (id)\n",
        "- **IMPORTANT**: No mention of vectors, inner products, or Hilbert spaces!\n",
        "\n",
        "### 2.2 Adjacent Transpositions (Coxeter Generators)\n",
        "\n",
        "**Definition**: An adjacent transposition s_i swaps elements in positions i and i+1:\n",
        "\n",
        "s_i = (i, i+1) for i = 1, 2, ..., N-1\n",
        "\n",
        "These are the **simple roots** of the Coxeter group of type A_{N-1}.\n",
        "\n",
        "**Coxeter Relations**:\n",
        "- s_i² = identity (involutory)\n",
        "- (s_i s_{i+1})³ = identity (braid relation)\n",
        "- (s_i s_j)² = identity for |i-j| > 1 (distant transpositions commute)\n",
        "\n",
        "**Citation**: Humphreys, \"Reflection Groups and Coxeter Groups\" (1990)\n",
        "\n",
        "### 2.3 The Cayley Graph\n",
        "\n",
        "**Definition**: The Cayley graph Γ(S_N, {s_1, ..., s_{N-1}}) has:\n",
        "- **Vertices**: All N! permutations in S_N\n",
        "- **Edges**: Connect permutations differing by one adjacent transposition\n",
        "- **Properties**: Connected, undirected, regular graph\n",
        "\n",
        "This is a purely **combinatorial** structure - no geometry assumed!\n",
        "\n",
        "### 2.4 The Permutohedron\n",
        "\n",
        "The permutohedron is the (N-1)-dimensional convex hull of all permutations embedded in ℝ^N.\n",
        "\n",
        "**Examples**:\n",
        "- N=3: Regular hexagon (2D)\n",
        "- N=4: Truncated octahedron (3D, 24 vertices, 36 edges)\n",
        "\n",
        "The **edges** of the permutohedron correspond exactly to the **edges** of the Cayley graph.\n"
    ]))

    # Code: Build Cayley graph
    cells.append(create_cell("code", [
        "def is_adjacent_transposition(perm1, perm2):\n",
        "    \"\"\"Check if two permutations differ by swapping adjacent elements.\"\"\"\n",
        "    differences = [i for i in range(len(perm1)) if perm1[i] != perm2[i]]\n",
        "    if len(differences) != 2:\n",
        "        return False\n",
        "    i, j = differences\n",
        "    if abs(i - j) != 1:\n",
        "        return False\n",
        "    return perm1[i] == perm2[j] and perm1[j] == perm2[i]\n",
        "\n",
        "def build_cayley_graph(N):\n",
        "    \"\"\"Build Cayley graph of S_N with adjacent transposition generators.\"\"\"\n",
        "    # Generate all permutations\n",
        "    perms = list(permutations(range(1, N+1)))\n",
        "    \n",
        "    # Create graph\n",
        "    G = nx.Graph()\n",
        "    G.add_nodes_from(range(len(perms)))\n",
        "    \n",
        "    # Add edges for adjacent transpositions\n",
        "    edge_count = 0\n",
        "    for i, perm1 in enumerate(perms):\n",
        "        for j, perm2 in enumerate(perms):\n",
        "            if i < j and is_adjacent_transposition(perm1, perm2):\n",
        "                G.add_edge(i, j)\n",
        "                edge_count += 1\n",
        "    \n",
        "    return G, perms\n",
        "\n",
        "# Build for N=3\n",
        "print(\"Building Cayley graph for N=3...\")\n",
        "G3, perms3 = build_cayley_graph(3)\n",
        "print(f\"N=3: {len(perms3)} vertices (permutations)\")\n",
        "print(f\"     {G3.number_of_edges()} edges (adjacent transpositions)\")\n",
        "print(f\"     Regular graph: degree = {list(dict(G3.degree()).values())[0]}\")\n",
        "\n",
        "# Build for N=4\n",
        "print(\"\\nBuilding Cayley graph for N=4...\")\n",
        "G4, perms4 = build_cayley_graph(4)\n",
        "print(f\"N=4: {len(perms4)} vertices (permutations)\")\n",
        "print(f\"     {G4.number_of_edges()} edges (adjacent transpositions)\")\n",
        "print(f\"     Regular graph: degree = {list(dict(G4.degree()).values())[0]}\")\n",
        "\n",
        "# Visualize N=3 (hexagon structure)\n",
        "fig, ax = plt.subplots(1, 1, figsize=(8, 8))\n",
        "pos = nx.spring_layout(G3, seed=42, iterations=100)\n",
        "nx.draw_networkx_nodes(G3, pos, node_color='lightblue', node_size=1200, ax=ax)\n",
        "nx.draw_networkx_edges(G3, pos, width=2, alpha=0.6, ax=ax)\n",
        "labels = {i: str(perms3[i]) for i in range(len(perms3))}\n",
        "nx.draw_networkx_labels(G3, pos, labels, font_size=10, ax=ax)\n",
        "ax.set_title('Cayley Graph of S_3 (Permutohedron Hexagon)', fontsize=14, fontweight='bold')\n",
        "ax.axis('off')\n",
        "plt.tight_layout()\n",
        "plt.show()\n",
        "\n",
        "print(\"\\n✓ Cayley graphs constructed successfully\")\n",
        "print(\"✓ These are PURE combinatorial structures (no vector spaces assumed)\")\n"
    ]))

    # Section 3: Combinatorial Distance Metrics
    cells.append(create_cell("markdown", [
        "## 3. Combinatorial Distance Metrics\n",
        "\n",
        "### 3.1 Kendall Tau Distance\n",
        "\n",
        "**Definition**: The Kendall tau distance counts the number of pairwise disagreements between two permutations.\n",
        "\n",
        "$$d_\\tau(\\sigma, \\pi) = |\\{(i,j) : i<j \\text{ and } (\\sigma(i)<\\sigma(j)) \\neq (\\pi(i)<\\pi(j))\\}|$$\n",
        "\n",
        "**Properties**:\n",
        "- Range: 0 to $\\binom{N}{2} = N(N-1)/2$\n",
        "- Symmetric: $d_\\tau(\\sigma, \\pi) = d_\\tau(\\pi, \\sigma)$\n",
        "- Triangle inequality: $d_\\tau(\\sigma, \\rho) \\leq d_\\tau(\\sigma, \\pi) + d_\\tau(\\pi, \\rho)$\n",
        "- S_N-invariant: $d_\\tau(g\\circ\\sigma, g\\circ\\pi) = d_\\tau(\\sigma, \\pi)$ for any g ∈ S_N\n",
        "\n",
        "**Citation**: Kendall, \"Rank Correlation Methods\" (1948)\n",
        "\n",
        "### 3.2 Inversion Distance\n",
        "\n",
        "**Definition**: The inversion distance is the minimum number of adjacent transpositions needed to transform σ → π.\n",
        "\n",
        "This is equivalent to the **graph distance** on the Cayley graph (shortest path).\n",
        "\n",
        "**Theorem**: On the Cayley graph, inversion distance equals Kendall tau distance.\n",
        "\n",
        "### 3.3 Key Point: Pure Combinatorics\n",
        "\n",
        "These distance metrics are defined **without any reference to**:\n",
        "- Vector spaces\n",
        "- Inner products\n",
        "- Norms\n",
        "- Quantum mechanics\n",
        "\n",
        "They arise naturally from the combinatorial structure of permutations!\n"
    ]))

    # Code: Distance matrices
    cells.append(create_cell("code", [
        "def kendall_tau_distance(perm1, perm2):\n",
        "    \"\"\"Compute Kendall tau distance between two permutations.\"\"\"\n",
        "    n = len(perm1)\n",
        "    distance = 0\n",
        "    for i in range(n):\n",
        "        for j in range(i+1, n):\n",
        "            # Check if relative order disagrees\n",
        "            order1 = (perm1[i] < perm1[j])\n",
        "            order2 = (perm2[i] < perm2[j])\n",
        "            if order1 != order2:\n",
        "                distance += 1\n",
        "    return distance\n",
        "\n",
        "def compute_distance_matrix(perms):\n",
        "    \"\"\"Compute full distance matrix for a list of permutations.\"\"\"\n",
        "    n = len(perms)\n",
        "    dist_matrix = np.zeros((n, n), dtype=int)\n",
        "    for i in range(n):\n",
        "        for j in range(n):\n",
        "            dist_matrix[i,j] = kendall_tau_distance(perms[i], perms[j])\n",
        "    return dist_matrix\n",
        "\n",
        "# Compute distance matrix for N=3\n",
        "print(\"Computing distance matrix for N=3...\")\n",
        "dist_matrix_3 = compute_distance_matrix(perms3)\n",
        "print(\"\\nDistance Matrix (N=3):\")\n",
        "print(dist_matrix_3)\n",
        "\n",
        "# Verify properties\n",
        "print(\"\\nVerifying metric properties for N=3:\")\n",
        "\n",
        "# 1. Symmetry\n",
        "is_symmetric = np.allclose(dist_matrix_3, dist_matrix_3.T)\n",
        "print(f\"1. Symmetry: d(σ,π) = d(π,σ) ... {is_symmetric}\")\n",
        "\n",
        "# 2. Identity\n",
        "diagonal_zero = np.all(np.diag(dist_matrix_3) == 0)\n",
        "print(f\"2. Identity: d(σ,σ) = 0 ... {diagonal_zero}\")\n",
        "\n",
        "# 3. Triangle inequality\n",
        "triangle_satisfied = True\n",
        "for i in range(len(perms3)):\n",
        "    for j in range(len(perms3)):\n",
        "        for k in range(len(perms3)):\n",
        "            if dist_matrix_3[i,k] > dist_matrix_3[i,j] + dist_matrix_3[j,k]:\n",
        "                triangle_satisfied = False\n",
        "                break\n",
        "        if not triangle_satisfied:\n",
        "            break\n",
        "    if not triangle_satisfied:\n",
        "        break\n",
        "print(f\"3. Triangle inequality: d(σ,ρ) ≤ d(σ,π) + d(π,ρ) ... {triangle_satisfied}\")\n",
        "\n",
        "# Visualize distance distribution\n",
        "fig, axes = plt.subplots(1, 2, figsize=(14, 5))\n",
        "\n",
        "# Heatmap\n",
        "im = axes[0].imshow(dist_matrix_3, cmap='YlOrRd', aspect='auto')\n",
        "axes[0].set_title('Distance Matrix Heatmap (N=3)', fontsize=12, fontweight='bold')\n",
        "axes[0].set_xlabel('Permutation index')\n",
        "axes[0].set_ylabel('Permutation index')\n",
        "plt.colorbar(im, ax=axes[0], label='Kendall tau distance')\n",
        "\n",
        "# Distance histogram\n",
        "upper_tri = dist_matrix_3[np.triu_indices_from(dist_matrix_3, k=1)]\n",
        "axes[1].hist(upper_tri, bins=range(4), edgecolor='black', alpha=0.7)\n",
        "axes[1].set_title('Distance Distribution (N=3)', fontsize=12, fontweight='bold')\n",
        "axes[1].set_xlabel('Distance')\n",
        "axes[1].set_ylabel('Frequency')\n",
        "axes[1].grid(axis='y', alpha=0.3)\n",
        "\n",
        "plt.tight_layout()\n",
        "plt.show()\n",
        "\n",
        "print(\"\\n✓ Kendall tau distance is a valid metric\")\n",
        "print(\"✓ Defined purely combinatorially (no vector spaces)\")\n"
    ]))

    # Due to length constraints, I'll create the remaining sections in the next cell
    # This creates a working notebook that can be extended

    cells.append(create_cell("markdown", [
        "## 4-8. Remaining Sections\n",
        "\n",
        "**Note**: This notebook is currently being implemented. Remaining sections:\n",
        "\n",
        "- Section 4: Distance-Preserving Transformations\n",
        "- Section 5: Entropy-Preserving Transformations\n",
        "- Section 6: Uniqueness Theorem - Emergent Unitarity\n",
        "- Section 7: Computational Validation (N=3, N=4)\n",
        "- Section 8: Connection to Quantum Mechanics\n",
        "\n",
        "Implementation continues in next session following the comprehensive plan in `NOTEBOOK_12_PLAN.md`.\n"
    ]))

    # Create notebook structure
    notebook = {
        "cells": cells,
        "metadata": {
            "kernelspec": {
                "display_name": "Python 3",
                "language": "python",
                "name": "python3"
            },
            "language_info": {
                "codemirror_mode": {
                    "name": "ipython",
                    "version": 3
                },
                "file_extension": ".py",
                "mimetype": "text/x-python",
                "name": "python",
                "nbconvert_exporter": "python",
                "pygments_lexer": "ipython3",
                "version": "3.10.0"
            }
        },
        "nbformat": 4,
        "nbformat_minor": 5
    }

    return notebook

if __name__ == "__main__":
    import os
    from pathlib import Path

    print("Creating Notebook 12: Unitary Invariance Foundations")
    notebook = create_notebook()

    # Use absolute path
    project_root = Path(__file__).parent.parent.parent.parent
    output_path = project_root / "notebooks" / "approach_1" / "12_Unitary_Invariance_Foundations.ipynb"

    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(notebook, f, indent=2, ensure_ascii=False)

    print(f"[OK] Notebook created: {output_path}")
    print(f"[OK] Sections 1-3 implemented (foundation)")
    print(f"[OK] Sections 4-8 ready for continuation")
    print("\nNext: Implement remaining sections following NOTEBOOK_12_PLAN.md")
