"""
Generate Figure 4: Triple Proof Convergence Diagram
Shows how three independent mathematical frameworks converge on K(N) = N-2

For Logic Field Theory publication
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Circle
import numpy as np

# Publication settings
plt.rcParams['font.family'] = 'serif'
plt.rcParams['font.serif'] = ['Times New Roman']
plt.rcParams['font.size'] = 10
plt.rcParams['mathtext.fontset'] = 'stix'

# Create figure
fig = plt.figure(figsize=(10, 8))
ax = fig.add_subplot(111)
ax.set_xlim(0, 10)
ax.set_ylim(0, 10)
ax.axis('off')

# Colors for three frameworks
color_combinatorics = '#2E86AB'  # Blue
color_algebra = '#A23B72'        # Purple
color_information = '#F18F01'    # Orange
color_result = '#C73E1D'         # Red

# ============================================
# THREE FRAMEWORK BOXES (Top Row)
# ============================================

# Box 1: Combinatorics (Mahonian)
box1_x, box1_y = 0.5, 7.5
box1_width, box1_height = 2.5, 2

# Framework box
mahonian_box = FancyBboxPatch(
    (box1_x, box1_y), box1_width, box1_height,
    boxstyle="round,pad=0.1",
    edgecolor=color_combinatorics,
    facecolor=color_combinatorics,
    alpha=0.15,
    linewidth=2.5
)
ax.add_patch(mahonian_box)

# Title
ax.text(box1_x + box1_width/2, box1_y + box1_height - 0.3,
        'Combinatorics',
        fontsize=12, fontweight='bold',
        ha='center', color=color_combinatorics)

# Content
ax.text(box1_x + box1_width/2, box1_y + box1_height/2 + 0.3,
        'Mahonian Symmetry',
        fontsize=10, ha='center', style='italic')
ax.text(box1_x + box1_width/2, box1_y + box1_height/2 - 0.2,
        r'Reversal bijection $\varphi(\sigma)$',
        fontsize=9, ha='center')
ax.text(box1_x + box1_width/2, box1_y + box1_height/2 - 0.7,
        r'$|V_{N-2}| = |V^c_{N-2}|$',
        fontsize=10, ha='center', fontweight='bold')

# Mini visualization: symmetric distribution
x_mini = np.linspace(box1_x + 0.3, box1_x + box1_width - 0.3, 7)
y_vals = np.array([1, 3, 6, 7, 6, 3, 1])  # Symmetric
y_mini = box1_y + 0.4 + 0.15 * y_vals / 7
ax.plot(x_mini, y_mini, 'o-', color=color_combinatorics, markersize=4, linewidth=1.5)
ax.axvline(box1_x + box1_width/2, ymin=0.08, ymax=0.22,
           color=color_combinatorics, linestyle='--', linewidth=1, alpha=0.5)

# Box 2: Algebra (Coxeter)
box2_x, box2_y = 3.75, 7.5

coxeter_box = FancyBboxPatch(
    (box2_x, box2_y), box1_width, box1_height,
    boxstyle="round,pad=0.1",
    edgecolor=color_algebra,
    facecolor=color_algebra,
    alpha=0.15,
    linewidth=2.5
)
ax.add_patch(coxeter_box)

ax.text(box2_x + box1_width/2, box2_y + box1_height - 0.3,
        'Algebra',
        fontsize=12, fontweight='bold',
        ha='center', color=color_algebra)

ax.text(box2_x + box1_width/2, box2_y + box1_height/2 + 0.3,
        'Coxeter Groups',
        fontsize=10, ha='center', style='italic')
ax.text(box2_x + box1_width/2, box2_y + box1_height/2 - 0.2,
        r'Braid relations $(s_i s_{i+1})^3 = e$',
        fontsize=9, ha='center')
ax.text(box2_x + box1_width/2, box2_y + box1_height/2 - 0.7,
        r'$\#\{\text{braid relations}\} = N-2$',
        fontsize=9, ha='center', fontweight='bold')

# Mini visualization: braid diagram (simplified)
y_braid = box2_y + 0.6
for i in range(3):
    x_start = box2_x + 0.5 + i*0.7
    # Crossing strands
    ax.plot([x_start, x_start + 0.7], [y_braid, y_braid + 0.4],
            color=color_algebra, linewidth=2)
    ax.plot([x_start + 0.7, x_start], [y_braid, y_braid + 0.4],
            color=color_algebra, linewidth=2, alpha=0.3)

# Box 3: Information Theory (MaxEnt)
box3_x, box3_y = 7.0, 7.5

maxent_box = FancyBboxPatch(
    (box3_x, box3_y), box1_width, box1_height,
    boxstyle="round,pad=0.1",
    edgecolor=color_information,
    facecolor=color_information,
    alpha=0.15,
    linewidth=2.5
)
ax.add_patch(maxent_box)

ax.text(box3_x + box1_width/2, box3_y + box1_height - 0.3,
        'Information',
        fontsize=12, fontweight='bold',
        ha='center', color=color_information)

ax.text(box3_x + box1_width/2, box3_y + box1_height/2 + 0.3,
        'Maximum Entropy',
        fontsize=10, ha='center', style='italic')
ax.text(box3_x + box1_width/2, box3_y + box1_height/2 - 0.2,
        r'Symmetry preservation',
        fontsize=9, ha='center')
ax.text(box3_x + box1_width/2, box3_y + box1_height/2 - 0.7,
        r'MaxEnt $\rightarrow$ K = N-2',
        fontsize=10, ha='center', fontweight='bold')

# Mini visualization: entropy curve
x_ent = np.linspace(box3_x + 0.3, box3_x + box1_width - 0.3, 30)
y_ent = box3_y + 0.7 + 0.4 * np.exp(-((x_ent - (box3_x + box1_width/2))/0.5)**2)
ax.plot(x_ent, y_ent, color=color_information, linewidth=2)
ax.plot(box3_x + box1_width/2, box3_y + 1.1, 'o',
        color=color_information, markersize=8, markeredgecolor='black', markeredgewidth=1)

# ============================================
# CONVERGENCE ARROWS
# ============================================

# Arrow from Box 1 (Combinatorics)
arrow1 = FancyArrowPatch(
    (box1_x + box1_width/2, box1_y),
    (5, 4.5),
    arrowstyle='->,head_width=0.4,head_length=0.4',
    color=color_combinatorics,
    linewidth=3,
    connectionstyle="arc3,rad=0.2"
)
ax.add_patch(arrow1)

# Arrow from Box 2 (Algebra)
arrow2 = FancyArrowPatch(
    (box2_x + box1_width/2, box2_y),
    (5, 4.5),
    arrowstyle='->,head_width=0.4,head_length=0.4',
    color=color_algebra,
    linewidth=3,
    connectionstyle="arc3,rad=0"
)
ax.add_patch(arrow2)

# Arrow from Box 3 (Information)
arrow3 = FancyArrowPatch(
    (box3_x + box1_width/2, box3_y),
    (5, 4.5),
    arrowstyle='->,head_width=0.4,head_length=0.4',
    color=color_information,
    linewidth=3,
    connectionstyle="arc3,rad=-0.2"
)
ax.add_patch(arrow3)

# ============================================
# CENTRAL RESULT CIRCLE
# ============================================

# Large circle for K = N-2
result_circle = Circle(
    (5, 3),
    radius=1.2,
    edgecolor=color_result,
    facecolor='white',
    linewidth=4,
    zorder=10
)
ax.add_patch(result_circle)

# Inner glow effect
for r in np.linspace(1.2, 1.4, 5):
    glow_circle = Circle(
        (5, 3),
        radius=r,
        edgecolor=color_result,
        facecolor='none',
        linewidth=1,
        alpha=0.3 * (1.4 - r) / 0.2,
        zorder=9
    )
    ax.add_patch(glow_circle)

# Main result text
ax.text(5, 3.3, r'$K(N) = N - 2$',
        fontsize=18, fontweight='bold', ha='center', va='center',
        color=color_result, zorder=11)
ax.text(5, 2.6, 'Multiply-Determined',
        fontsize=10, ha='center', va='center', style='italic',
        color='black', zorder=11)

# ============================================
# BOTTOM: IMPLICATIONS
# ============================================

implications_y = 1.2
ax.text(5, implications_y + 0.5, 'Implications',
        fontsize=11, fontweight='bold', ha='center',
        color='black')

# Three implications boxes
impl_width = 2.8
impl_height = 0.6
impl_spacing = 0.15

# Implication 1
impl1_x = 5 - impl_width - impl_spacing
impl_box1 = FancyBboxPatch(
    (impl1_x, implications_y - impl_height), impl_width, impl_height,
    boxstyle="round,pad=0.05",
    edgecolor='gray',
    facecolor='lightgray',
    alpha=0.3,
    linewidth=1.5
)
ax.add_patch(impl_box1)
ax.text(impl1_x + impl_width/2, implications_y - impl_height/2,
        r'Not empirical parameter',
        fontsize=9, ha='center', va='center')

# Implication 2
impl2_x = 5 - impl_width/2
impl_box2 = FancyBboxPatch(
    (impl2_x, implications_y - impl_height), impl_width, impl_height,
    boxstyle="round,pad=0.05",
    edgecolor='gray',
    facecolor='lightgray',
    alpha=0.3,
    linewidth=1.5
)
ax.add_patch(impl_box2)
ax.text(impl2_x + impl_width/2, implications_y - impl_height/2,
        r'Mathematical necessity',
        fontsize=9, ha='center', va='center', fontweight='bold')

# Implication 3
impl3_x = 5 + impl_spacing
impl_box3 = FancyBboxPatch(
    (impl3_x, implications_y - impl_height), impl_width, impl_height,
    boxstyle="round,pad=0.05",
    edgecolor='gray',
    facecolor='lightgray',
    alpha=0.3,
    linewidth=1.5
)
ax.add_patch(impl_box3)
ax.text(impl3_x + impl_width/2, implications_y - impl_height/2,
        r'Completes Born rule derivation',
        fontsize=9, ha='center', va='center')

# ============================================
# TITLE
# ============================================

ax.text(5, 9.7, 'Triple Proof Convergence: K(N) = N - 2',
        fontsize=14, fontweight='bold', ha='center')
ax.text(5, 9.3, 'Three independent frameworks establish multiply-determined necessity',
        fontsize=10, ha='center', style='italic', color='gray')

plt.tight_layout()

# Save figure
output_file = '../paper/figures/figure4_triple_convergence.png'
plt.savefig(output_file, dpi=300, bbox_inches='tight', facecolor='white')
print(f"[OK] Figure 4 saved: {output_file}")

# Also save high-res version
output_file_hires = '../paper/figures/figure4_triple_convergence_hires.png'
plt.savefig(output_file_hires, dpi=600, bbox_inches='tight', facecolor='white')
print(f"[OK] High-res version saved: {output_file_hires}")

plt.close()

print("\n=== Figure 4 Generation Complete ===")
print("Triple proof convergence diagram created")
print("Shows: Combinatorics + Algebra + Information -> K = N-2")
