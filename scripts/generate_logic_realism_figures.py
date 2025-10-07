"""
Generate supporting figures for Logic Realism Foundational Paper
Creates 5 key visualizations illustrating core concepts
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
from mpl_toolkits.mplot3d import Axes3D
import networkx as nx
from itertools import permutations

# Set style
plt.style.use('seaborn-v0_8-paper')
colors = {'primary': '#2E86AB', 'secondary': '#A23B72', 'accent': '#F18F01',
          'valid': '#06A77D', 'invalid': '#D62246'}

def inversion_count(perm):
    """Count inversions in a permutation"""
    count = 0
    for i in range(len(perm)):
        for j in range(i + 1, len(perm)):
            if perm[i] > perm[j]:
                count += 1
    return count

# =============================================================================
# Figure 1: Information-Logic Mapping (A = L(I))
# =============================================================================
def create_figure1_mapping():
    """Conceptual diagram of I → L → A"""
    fig, ax = plt.subplots(1, 1, figsize=(12, 6))
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 5)
    ax.axis('off')

    # Infinite Information Space (I)
    box1 = FancyBboxPatch((0.5, 1.5), 2, 2, boxstyle="round,pad=0.1",
                           edgecolor=colors['primary'], facecolor=colors['primary'],
                           alpha=0.2, linewidth=2)
    ax.add_patch(box1)
    ax.text(1.5, 2.5, r'$\mathbb{I}$', fontsize=24, ha='center', va='center', weight='bold')
    ax.text(1.5, 1.8, 'Infinite\nInformation\nSpace', fontsize=10, ha='center', va='center')
    ax.text(1.5, 0.8, r'All conceivable $\sigma \in \prod S_N$', fontsize=9, ha='center', style='italic')

    # Logical Field (L)
    circle = plt.Circle((5, 2.5), 0.8, color=colors['accent'], alpha=0.3, linewidth=2,
                       edgecolor=colors['accent'])
    ax.add_patch(circle)
    ax.text(5, 2.5, r'$\mathcal{L}$', fontsize=24, ha='center', va='center', weight='bold')
    ax.text(5, 1.3, 'Logical Field', fontsize=10, ha='center', va='center')
    ax.text(5, 0.8, r'Enforces ID, NC, EM', fontsize=9, ha='center', style='italic')

    # Actualized Reality (A)
    box2 = FancyBboxPatch((7.5, 1.5), 2, 2, boxstyle="round,pad=0.1",
                           edgecolor=colors['valid'], facecolor=colors['valid'],
                           alpha=0.2, linewidth=2)
    ax.add_patch(box2)
    ax.text(8.5, 2.5, r'$A$', fontsize=24, ha='center', va='center', weight='bold')
    ax.text(8.5, 1.8, 'Actualized\nReality', fontsize=10, ha='center', va='center')
    ax.text(8.5, 0.8, r'$V_K = \{\sigma : h(\sigma) \leq K\}$', fontsize=9, ha='center', style='italic')

    # Arrows
    arrow1 = FancyArrowPatch((2.6, 2.5), (4.1, 2.5), arrowstyle='->', lw=3,
                            color=colors['primary'], mutation_scale=30)
    ax.add_artist(arrow1)
    ax.text(3.35, 3.2, r'Filter $L$', fontsize=12, ha='center', weight='bold')

    arrow2 = FancyArrowPatch((5.9, 2.5), (7.4, 2.5), arrowstyle='->', lw=3,
                            color=colors['valid'], mutation_scale=30)
    ax.add_artist(arrow2)
    ax.text(6.65, 3.2, r'Select', fontsize=12, ha='center', weight='bold')

    # Main equation
    ax.text(5, 4.5, r'$A = L(\mathbb{I})$', fontsize=28, ha='center', weight='bold',
           bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))

    plt.title('Figure 1: The Information-Logic Mapping', fontsize=16, weight='bold', pad=20)
    plt.tight_layout()
    plt.savefig('paper/figures/logic_realism_fig1_mapping.png', dpi=300, bbox_inches='tight')
    plt.savefig('paper/figures/logic_realism_fig1_mapping.svg', bbox_inches='tight')
    print("[OK] Figure 1 created: Information-Logic Mapping")

# =============================================================================
# Figure 2: Logical Constraint Structure h(σ) ≤ K
# =============================================================================
def create_figure2_constraint():
    """Histogram of inversion counts with K=N-2 threshold"""
    N = 5
    K = N - 2  # = 3

    # Generate all permutations and compute h(σ)
    all_perms = list(permutations(range(N)))
    h_values = [inversion_count(p) for p in all_perms]

    fig, ax = plt.subplots(1, 1, figsize=(10, 6))

    # Create histogram
    bins = np.arange(-0.5, max(h_values) + 1.5, 1)
    counts, edges, patches = ax.hist(h_values, bins=bins, edgecolor='black', alpha=0.7)

    # Color valid vs invalid
    for i, patch in enumerate(patches):
        if i <= K:
            patch.set_facecolor(colors['valid'])
        else:
            patch.set_facecolor(colors['invalid'])

    # Add threshold line
    ax.axvline(K + 0.5, color='red', linestyle='--', linewidth=3, label=f'K(N) = {K}')

    # Annotations
    ax.text(K/2, max(counts)*0.9, f'Valid States\n$V_K$\n({sum(1 for h in h_values if h <= K)} perms)',
           ha='center', fontsize=12, weight='bold',
           bbox=dict(boxstyle='round', facecolor=colors['valid'], alpha=0.3))

    ax.text((K + max(h_values))/2 + 0.5, max(counts)*0.9,
           f'Excluded\n({sum(1 for h in h_values if h > K)} perms)',
           ha='center', fontsize=12, weight='bold',
           bbox=dict(boxstyle='round', facecolor=colors['invalid'], alpha=0.3))

    ax.set_xlabel(r'Inversion Count $h(\sigma)$', fontsize=14, weight='bold')
    ax.set_ylabel('Number of Permutations', fontsize=14, weight='bold')
    ax.set_title(f'Figure 2: Logical Constraint Structure (N={N}, K={K})',
                fontsize=16, weight='bold', pad=15)
    ax.legend(fontsize=12)
    ax.grid(alpha=0.3)

    plt.tight_layout()
    plt.savefig('paper/figures/logic_realism_fig2_constraint.png', dpi=300, bbox_inches='tight')
    plt.savefig('paper/figures/logic_realism_fig2_constraint.svg', bbox_inches='tight')
    print("[OK] Figure 2 created: Logical Constraint Structure")

# =============================================================================
# Figure 3: Entropy-Amplitude Bridge
# =============================================================================
def create_figure3_entropy_amplitude():
    """Flow diagram showing P → |a|² transformation"""
    fig, ax = plt.subplots(1, 1, figsize=(12, 8))
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)
    ax.axis('off')

    # Box 1: MaxEnt Probability
    box1 = FancyBboxPatch((0.5, 7), 3, 2, boxstyle="round,pad=0.1",
                          edgecolor=colors['primary'], facecolor=colors['primary'],
                          alpha=0.2, linewidth=2)
    ax.add_patch(box1)
    ax.text(2, 8.5, 'MaxEnt on $V_K$', fontsize=13, ha='center', weight='bold')
    ax.text(2, 8, r'$P(\sigma) = \frac{1}{|V_K|}$', fontsize=14, ha='center')

    # Box 2: Complex Amplitudes
    box2 = FancyBboxPatch((6.5, 7), 3, 2, boxstyle="round,pad=0.1",
                          edgecolor=colors['valid'], facecolor=colors['valid'],
                          alpha=0.2, linewidth=2)
    ax.add_patch(box2)
    ax.text(8, 8.5, 'Quantum Amplitudes', fontsize=13, ha='center', weight='bold')
    ax.text(8, 8, r'$a_\sigma \in \mathbb{C}$', fontsize=14, ha='center')

    # Arrow with constraints
    arrow = FancyArrowPatch((3.6, 8), (6.4, 8), arrowstyle='->', lw=4,
                           color=colors['accent'], mutation_scale=30)
    ax.add_artist(arrow)
    ax.text(5, 8.7, 'Entropy-Amplitude Bridge', fontsize=12, ha='center', weight='bold',
           bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))

    # Three constraints (vertical stack)
    constraints = [
        (r'1. Normalization: $\sum |a_\sigma|^2 = 1$', 5.5),
        (r'2. Entropy: $H[P] = H[|a|^2]$ maximized', 4.5),
        (r'3. Unitary: $U^\dagger U = I$ invariance', 3.5)
    ]

    for text, y in constraints:
        box = FancyBboxPatch((1, y-0.3), 8, 0.6, boxstyle="round,pad=0.05",
                            edgecolor=colors['accent'], facecolor='lightyellow',
                            alpha=0.5, linewidth=1)
        ax.add_patch(box)
        ax.text(5, y, text, fontsize=11, ha='center', va='center')

    # Uniqueness theorem box
    theorem_box = FancyBboxPatch((1.5, 1), 7, 1.5, boxstyle="round,pad=0.1",
                                edgecolor='darkred', facecolor='lightcoral',
                                alpha=0.2, linewidth=2)
    ax.add_patch(theorem_box)
    ax.text(5, 2.1, r'\textbf{Theorem 5.1 (Uniqueness):}', fontsize=12, ha='center', weight='bold')
    ax.text(5, 1.6, r'$P(\sigma) = |a_\sigma|^2$ is the unique solution', fontsize=11, ha='center')
    ax.text(5, 1.2, r'(up to global phase)', fontsize=10, ha='center', style='italic')

    # Born rule
    ax.text(5, 0.3, r'$\Rightarrow$ \textbf{Born Rule:} $P = |a|^2$', fontsize=16, ha='center',
           weight='bold', bbox=dict(boxstyle='round', facecolor='gold', alpha=0.4))

    plt.title('Figure 3: The Entropy-Amplitude Bridge', fontsize=16, weight='bold', pad=20)
    plt.tight_layout()
    plt.savefig('paper/figures/logic_realism_fig3_entropy_amplitude.png', dpi=300, bbox_inches='tight')
    plt.savefig('paper/figures/logic_realism_fig3_entropy_amplitude.svg', bbox_inches='tight')
    print("[OK] Figure 3 created: Entropy-Amplitude Bridge")

# =============================================================================
# Figure 4: Lagrangian-Hamiltonian Duality
# =============================================================================
def create_figure4_duality():
    """Diagram showing L ↔ H duality via Legendre transform"""
    fig, ax = plt.subplots(1, 1, figsize=(12, 8))
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)
    ax.axis('off')

    # Lagrangian side (left)
    lagrangian_box = FancyBboxPatch((0.5, 5.5), 4, 3, boxstyle="round,pad=0.15",
                                    edgecolor=colors['primary'], facecolor=colors['primary'],
                                    alpha=0.15, linewidth=3)
    ax.add_patch(lagrangian_box)
    ax.text(2.5, 8.2, r'\textbf{Lagrangian Formulation}', fontsize=14, ha='center', weight='bold')
    ax.text(2.5, 7.6, r'$L = \frac{\chi}{2}\dot{h}^2 - \frac{\mu^2}{2}h^2$', fontsize=13, ha='center')
    ax.text(2.5, 7.0, r'Action: $S = \int L \, dt$', fontsize=11, ha='center')
    ax.text(2.5, 6.4, r'Principle: $\delta S = 0$', fontsize=11, ha='center')
    ax.text(2.5, 5.9, r'(Minimal Inconsistency)', fontsize=10, ha='center', style='italic')

    # Hamiltonian side (right)
    hamiltonian_box = FancyBboxPatch((5.5, 5.5), 4, 3, boxstyle="round,pad=0.15",
                                     edgecolor=colors['valid'], facecolor=colors['valid'],
                                     alpha=0.15, linewidth=3)
    ax.add_patch(hamiltonian_box)
    ax.text(7.5, 8.2, r'\textbf{Hamiltonian Formulation}', fontsize=14, ha='center', weight='bold')
    ax.text(7.5, 7.6, r'$\hat{H} = D - A$', fontsize=13, ha='center')
    ax.text(7.5, 7.0, r'(Graph Laplacian)', fontsize=11, ha='center')
    ax.text(7.5, 6.4, r'Dynamics: $i\hbar\partial_t|\psi\rangle = \hat{H}|\psi\rangle$', fontsize=11, ha='center')
    ax.text(7.5, 5.9, r'(Minimal Fisher Info)', fontsize=10, ha='center', style='italic')

    # Legendre transform (bidirectional)
    arrow1 = FancyArrowPatch((4.6, 7.5), (5.4, 7.5), arrowstyle='->', lw=3,
                            color=colors['accent'], mutation_scale=25)
    ax.add_artist(arrow1)
    arrow2 = FancyArrowPatch((5.4, 6.5), (4.6, 6.5), arrowstyle='->', lw=3,
                            color=colors['accent'], mutation_scale=25)
    ax.add_artist(arrow2)

    ax.text(5, 7.8, 'Legendre', fontsize=11, ha='center', weight='bold')
    ax.text(5, 7.5, r'$p = \partial L/\partial\dot{h}$', fontsize=10, ha='center')
    ax.text(5, 6.2, 'Transform', fontsize=11, ha='center', weight='bold')
    ax.text(5, 5.9, r'$H = p\dot{h} - L$', fontsize=10, ha='center')

    # Euler-Lagrange equation (bottom left)
    el_box = FancyBboxPatch((0.5, 3), 4, 1.8, boxstyle="round,pad=0.1",
                           edgecolor=colors['secondary'], facecolor='lavender',
                           alpha=0.4, linewidth=2)
    ax.add_patch(el_box)
    ax.text(2.5, 4.5, r'Euler-Lagrange:', fontsize=11, ha='center', weight='bold')
    ax.text(2.5, 4.0, r'$\chi\ddot{h} + \mu^2 h = 0$', fontsize=12, ha='center')
    ax.text(2.5, 3.4, r'(Wave equation on graph)', fontsize=9, ha='center', style='italic')

    # Hamilton's equations (bottom right)
    ham_box = FancyBboxPatch((5.5, 3), 4, 1.8, boxstyle="round,pad=0.1",
                            edgecolor=colors['secondary'], facecolor='lavender',
                            alpha=0.4, linewidth=2)
    ax.add_patch(ham_box)
    ax.text(7.5, 4.5, r"Hamilton's Equations:", fontsize=11, ha='center', weight='bold')
    ax.text(7.5, 4.0, r'$\dot{h} = \partial H/\partial p$', fontsize=11, ha='center')
    ax.text(7.5, 3.5, r'$\dot{p} = -\partial H/\partial h$', fontsize=11, ha='center')

    # Duality theorem (bottom center)
    duality_box = FancyBboxPatch((1.5, 0.5), 7, 2, boxstyle="round,pad=0.15",
                                edgecolor='darkred', facecolor='lightcoral',
                                alpha=0.2, linewidth=3)
    ax.add_patch(duality_box)
    ax.text(5, 2.1, r'\textbf{Theorem 6.1 (Duality):}', fontsize=13, ha='center', weight='bold')
    ax.text(5, 1.6, r'Minimal Inconsistency $\equiv$ Minimal Fisher Information', fontsize=12, ha='center')
    ax.text(5, 1.1, r'Lagrangian and Hamiltonian formulations are equivalent', fontsize=11, ha='center')
    ax.text(5, 0.7, r'via Legendre transform', fontsize=10, ha='center', style='italic')

    plt.title('Figure 4: Lagrangian-Hamiltonian Duality of Logical Dynamics',
             fontsize=16, weight='bold', pad=20)
    plt.tight_layout()
    plt.savefig('paper/figures/logic_realism_fig4_duality.png', dpi=300, bbox_inches='tight')
    plt.savefig('paper/figures/logic_realism_fig4_duality.svg', bbox_inches='tight')
    print("[OK] Figure 4 created: Lagrangian-Hamiltonian Duality")

# =============================================================================
# Figure 5: Permutohedron with V_K highlighted (N=4)
# =============================================================================
def create_figure5_permutohedron():
    """3D permutohedron for N=4 with valid states V_K highlighted"""
    N = 4
    K = N - 2  # = 2

    # Generate all permutations
    all_perms = list(permutations(range(1, N+1)))

    # Compute coordinates (standard permutohedron embedding)
    coords = {}
    for perm in all_perms:
        coords[perm] = np.array(perm)

    # Classify by h value
    valid_perms = [p for p in all_perms if inversion_count(p) <= K]
    invalid_perms = [p for p in all_perms if inversion_count(p) > K]

    # Create 3D plot
    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')

    # Plot valid vertices (green, larger)
    valid_coords = np.array([coords[p] for p in valid_perms])
    ax.scatter(valid_coords[:, 0], valid_coords[:, 1], valid_coords[:, 2],
              c=colors['valid'], s=200, alpha=0.8, edgecolors='black', linewidth=2,
              label=f'Valid States (h ≤ {K}): {len(valid_perms)} perms')

    # Plot invalid vertices (red, smaller)
    invalid_coords = np.array([coords[p] for p in invalid_perms])
    ax.scatter(invalid_coords[:, 0], invalid_coords[:, 1], invalid_coords[:, 2],
              c=colors['invalid'], s=100, alpha=0.5, edgecolors='gray', linewidth=1,
              label=f'Excluded (h > {K}): {len(invalid_perms)} perms')

    # Draw edges (faint)
    def are_adjacent(p1, p2):
        """Check if two permutations differ by one adjacent transposition"""
        diffs = sum(1 for i in range(len(p1)) if p1[i] != p2[i])
        if diffs != 2:
            return False
        # Check if swapped elements are adjacent
        diff_indices = [i for i in range(len(p1)) if p1[i] != p2[i]]
        return abs(diff_indices[0] - diff_indices[1]) == 1

    for i, p1 in enumerate(all_perms):
        for p2 in all_perms[i+1:]:
            if are_adjacent(p1, p2):
                c1, c2 = coords[p1], coords[p2]
                color = colors['valid'] if (p1 in valid_perms and p2 in valid_perms) else 'lightgray'
                alpha = 0.6 if (p1 in valid_perms and p2 in valid_perms) else 0.2
                linewidth = 1.5 if (p1 in valid_perms and p2 in valid_perms) else 0.5
                ax.plot([c1[0], c2[0]], [c1[1], c2[1]], [c1[2], c2[2]],
                       color=color, alpha=alpha, linewidth=linewidth)

    ax.set_xlabel('X', fontsize=12, weight='bold')
    ax.set_ylabel('Y', fontsize=12, weight='bold')
    ax.set_zlabel('Z', fontsize=12, weight='bold')
    ax.set_title(f'Figure 5: Permutohedron with Logical Constraint V_K (N={N}, K={K})',
                fontsize=16, weight='bold', pad=20)
    ax.legend(fontsize=11, loc='upper left')

    # Better viewing angle
    ax.view_init(elev=20, azim=45)

    plt.tight_layout()
    plt.savefig('paper/figures/logic_realism_fig5_permutohedron.png', dpi=300, bbox_inches='tight')
    plt.savefig('paper/figures/logic_realism_fig5_permutohedron.svg', bbox_inches='tight')
    print("[OK] Figure 5 created: Permutohedron with V_K")

# =============================================================================
# Main execution
# =============================================================================
if __name__ == "__main__":
    print("\nGenerating Logic Realism Foundational Paper Figures...")
    print("=" * 60)

    create_figure1_mapping()
    create_figure2_constraint()
    create_figure3_entropy_amplitude()
    create_figure4_duality()
    create_figure5_permutohedron()

    print("=" * 60)
    print("All figures generated successfully!")
    print("\nFigures saved to: paper/figures/")
    print("  - logic_realism_fig1_mapping.png/svg")
    print("  - logic_realism_fig2_constraint.png/svg")
    print("  - logic_realism_fig3_entropy_amplitude.png/svg")
    print("  - logic_realism_fig4_duality.png/svg")
    print("  - logic_realism_fig5_permutohedron.png/svg")
