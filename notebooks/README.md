# Logic Field Theory (LFT) - Notebooks

This folder contains the complete Jupyter notebook implementation of Logic Field Theory (LFT), a research program that derives the foundations of physics from a single logical axiom. The notebooks are structured to be read in sequence, building a cohesive narrative from philosophical motivation to formal derivations, computational verification, and finally, to novel, falsifiable predictions.

## Core Thesis

Logic Field Theory is built on a single generative axiom:
$$ A = L(I) $$
where **A**ctuality is the result of a **L**ogical operator (Identity ∘ Non-Contradiction ∘ Excluded Middle) filtering an infinite **I**nformation space of potential distinctions.

From this starting point, the LFT program derives the core features of our universe:
- The **3+1 dimensionality of spacetime**.
- A mechanistic **arrow of time**.
- The mathematical formalism of **quantum mechanics**, including the **Born Rule**.
- The **Tsirelson Bound** on quantum correlations.
- A toy model for **gravity** as an emergent effect of logical constraint.

---

## Notebook Sequence and Narrative Flow

The notebooks are numbered to guide the reader through the logical development of the theory.

### Part 00: Foundations & Motivation

This series lays the conceptual and philosophical groundwork for the entire project.
-   **`LFT_00a_v2_Foundations.ipynb`**: Introduces the core "logic-first" stance and the central axiom $A = L(I)$.
-   **`LFT_00_a1_Ontology_of_I.ipynb`**: Provides a formal ontology for the information space *I* as the space of all partial orders.
-   **`LFT_00b_From3FLL_to_ALI.ipynb`**: Translates the three fundamental laws of logic into a concrete, algorithmic operator *L*.
-   **`LFT_00c_Nminus1_Context.ipynb`**: Frames the central problem of dimensionality and defines the explicit success criteria that the rest of the project must meet.
-   **`LFT_00d_Origin_of_N.ipynb`**: Presents analytic, combinatorial, and dynamic evidence for why N=4 (leading to 3 dimensions) is a critical stability threshold.

### Part 1: Core Derivations - Geometry, Time, and the Quantum Bridge

This series executes the main constructive proofs of the theory.
-   **`LFT_01_Introduction.ipynb`**: A gentle introduction using the minimal non-trivial case of N=3 to verify the emergence of the correct geometry ($A_2$ root system, hexagonal permutohedron).
-   **`LFT_02_Geometry_Derivation.ipynb`**: The crucial step. Derives the 3D permutohedral stage for the N=4 case, verifying its geometric and algebraic properties (the $A_3$ Coxeter system).
-   **`LFT_03_Dynamics_Time.ipynb`**: Formalizes the **arrow of time** as a monotonic descent ("L-flow") on the geometric stage, governed by the order field $h(\sigma)$.
-   **`LFT_03_5_Logical_Strain_Dynamics_REV.ipynb`**: A revised, deeper look at the dynamics, defining logical strain and justifying Boltzmann-like weights from a maximum entropy principle.
-   **`LFT_04_Qudit_Bridge.ipynb`**: Establishes the formal link between the LFT geometry and the state space of a quantum system (a qudit).
-   **`LFT_05_N6_Scaling_Stress.ipynb` & `LFT_06_Spacetime_Test.ipynb`**: Scales the model up to N=6 to demonstrate the natural emergence of a **3+1 spacetime factorization** with high geometric fidelity.
-   **`LFT_07_Born_Rule_Formal.ipynb`**: A landmark result. Provides a formal derivation of the **Born Rule** from the physical process of "constraint counting," moving it from a postulate to a theorem.

### Part 2: Explanatory Power, Predictions, and Context

This final series demonstrates the power of the LFT framework by using it to resolve paradoxes, make new predictions, and connect to known physics.
-   **`LFT_08_Comparisons.ipynb`**: Positions LFT relative to other interpretations of quantum mechanics (e.g., Everett, Bohm) and foundational ideas (e.g., Wheeler's "It from Bit").
-   **`LFT_09_Explanatory_Power.ipynb`**: Shows how LFT provides clear, mechanistic resolutions to long-standing quantum paradoxes like the Measurement Problem, EPR, and Wigner's Friend.
-   **`LFT_10_Observer_revised.ipynb`**: Models the observer not as a special entity, but as a system that injects logical constraints, mechanistically explaining measurement, decoherence, and the Quantum Zeno effect.
-   **`LFT_11_Tsirelson_from_L.ipynb`**: Derives the Tsirelson bound ($|S| \le 2\sqrt{2}$) on quantum correlations as a direct consequence of the global logical consistency enforced by *L*, and proves that supra-quantum correlations are logically impossible.
-   **`LFT_12_Gravity_from_Constraint_Geometry.ipynb`**: Presents a proof-of-concept model for **gravity** as an emergent phenomenon, where matter (as constraint density) warps the logical geometry, causing time dilation and geodesic bending.
-   **`LFT_13_Predictive_Probes.ipynb`**: The capstone. Translates the theory into **novel, falsifiable predictions**, primarily the existence of **"finite-K effects"**—systematic deviations from the Born Rule and Bell's theorem that scale with measurement complexity and are absent in standard QM.

---

## How to Run

1.  **Dependencies**: The notebooks primarily use standard scientific Python libraries such as `numpy`, `scipy`, `networkx`, and `matplotlib`.
2.  **Execution Order**: It is highly recommended to review the notebooks in numerical order, starting with the `00` series, to follow the logical development of the theory.
3.  **Reproducibility**: Most notebooks use fixed random seeds for simulations to ensure that figures and quantitative results are reproducible.