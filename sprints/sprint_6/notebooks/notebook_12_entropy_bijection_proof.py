#!/usr/bin/env python3
"""
Script to strengthen the entropy→bijectivity analytical proof in Notebook 12.

This addresses critical team feedback from Consultation 2:
- Current: Computational validation only
- Needed: Rigorous proof that entropy preservation → bijection

The proof shows that any transformation preserving the entropy of the
uniform distribution MUST be bijective (both injective and surjective).
This uses information-theoretic arguments (Jensen's inequality, strict
concavity of entropy functional).
"""

import json
import sys

# New markdown cell with rigorous proof
ENTROPY_BIJECTION_PROOF = """### 5.2.1 Rigorous Proof: Entropy Preservation ⟹ Bijectivity

**Theorem**: Let T: S_N → S_N be a transformation. If T preserves the entropy of the uniform distribution, then T must be bijective.

**Proof**:

Let P be the uniform distribution on S_N:

$$p(\sigma) = \frac{1}{N!} \quad \forall \sigma \in S_N$$

Its entropy is:

$$H(P) = -\sum_{\sigma \in S_N} \frac{1}{N!} \log\left(\frac{1}{N!}\right) = \log(N!)$$

This is the **maximum possible entropy** for any distribution on N! elements.

**Step 1: Define the transformed distribution**

After applying T, the probability that element τ ∈ S_N appears is:

$$q(\tau) = \frac{1}{N!} \cdot |\{\sigma \in S_N : T(\sigma) = \tau\}|$$

Let $n_\tau = |\{\sigma : T(\sigma) = \tau\}|$ be the number of preimages of τ under T.

Then: $q(\tau) = \frac{n_\tau}{N!}$

**Step 2: Constraint from total probability**

$$\sum_{\tau \in S_N} q(\tau) = \sum_{\tau} \frac{n_\tau}{N!} = \frac{1}{N!} \sum_{\tau} n_\tau = \frac{N!}{N!} = 1$$

This implies: $\sum_{\tau} n_\tau = N!$ (total number of elements)

**Step 3: Entropy of transformed distribution**

$$H(Q) = -\sum_{\tau \in S_N} q(\tau) \log q(\tau) = -\sum_{\tau} \frac{n_\tau}{N!} \log\left(\frac{n_\tau}{N!}\right)$$

$$= -\frac{1}{N!} \sum_{\tau : n_\tau > 0} n_\tau \log\left(\frac{n_\tau}{N!}\right)$$

**Step 4: Apply Jensen's Inequality**

The entropy functional is **strictly concave** in the probability distribution. By Jensen's inequality, for any distribution Q:

$$H(Q) \leq H(P_\text{uniform}) = \log(N!)$$

with **equality if and only if Q is uniform**.

**Step 5: Condition for equality**

For H(Q) = H(P) = log(N!), we require Q to be uniform:

$$q(\tau) = \frac{1}{N!} \quad \forall \tau \in S_N$$

This means: $n_\tau = 1$ for all τ in the range of T.

**Step 6: Derive bijectivity**

From $n_\tau = 1$ for all τ in range(T):
- **Injectivity**: No two elements map to the same τ (each $n_\tau \leq 1$)
- **Surjectivity**: Since $\sum_\tau n_\tau = N!$ and each $n_\tau \in \{0,1\}$, we need exactly N! elements with $n_\tau = 1$. This means range(T) = S_N.

Therefore, T is bijective. **QED**

### 5.2.2 Why Non-Bijective Transformations Fail

**Case 1: T is not surjective** (some element τ₀ is never reached)

Then $n_{\tau_0} = 0$, so $q(\tau_0) = 0$. The sum $\sum_\tau n_\tau = N!$ must be distributed over fewer than N! elements, so some $n_\tau > 1$.

Result: Some probabilities become larger than 1/N!, making the distribution non-uniform, reducing entropy below log(N!).

**Case 2: T is not injective** (some element τ₀ has multiple preimages)

Then $n_{\tau_0} > 1$, so $q(\tau_0) > 1/N!$. By the constraint $\sum_\tau n_\tau = N!$, some other elements must have $n_\tau = 0$.

Result: Distribution becomes non-uniform (some probabilities > 1/N!, others = 0), reducing entropy.

### 5.2.3 Information-Theoretic Interpretation

**Key Insight**: The uniform distribution has **maximum uncertainty** (maximum entropy). Any transformation that creates:
- "Collisions" (multiple elements mapping to same output) → reduces uncertainty
- "Gaps" (unreachable outputs) → reduces uncertainty

Only a **bijection** preserves maximum uncertainty, hence preserves entropy!

**Connection to Information Theory** (Shannon 1948):
- Entropy measures information content
- Bijections preserve all information (reversible/lossless)
- Non-bijective maps lose information (irreversible/lossy)

**Citation**: Shannon, C.E. (1948). "A Mathematical Theory of Communication." *Bell System Technical Journal* 27: 379-423.
"""

def insert_entropy_bijection_proof(notebook_path):
    """Insert rigorous entropy→bijection proof into Notebook 12."""

    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    # Find the cell with "### 5.2 Entropy Preservation Requirement"
    insert_index = None
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] == 'markdown':
            content = ''.join(cell['source'])
            if '### 5.2 Entropy Preservation Requirement' in content:
                insert_index = i + 1  # Insert right after 5.2 header
                break

    if insert_index is None:
        print("ERROR: Could not find Section 5.2 in notebook")
        return False

    # Create new cell with rigorous proof
    proof_cell = {
        'cell_type': 'markdown',
        'metadata': {},
        'source': ENTROPY_BIJECTION_PROOF.split('\n')
    }

    # Insert cell
    nb['cells'].insert(insert_index, proof_cell)

    # Update subsequent subsection numbering (5.3 → 5.4)
    for i in range(insert_index + 1, len(nb['cells'])):
        if nb['cells'][i]['cell_type'] == 'markdown':
            content = ''.join(nb['cells'][i]['source'])

            # Update 5.3 Combined Constraints → 5.4 Combined Constraints
            if '### 5.3 Combined Constraints' in content:
                nb['cells'][i]['source'] = [line.replace('### 5.3 Combined Constraints',
                                                          '### 5.4 Combined Constraints')
                                             for line in nb['cells'][i]['source']]
                break  # Only one subsection to rename

    # Write updated notebook
    with open(notebook_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)

    print("✓ Added rigorous entropy→bijectivity proof")
    print("✓ Proof includes:")
    print("  - Theorem statement and complete proof")
    print("  - Jensen's inequality application")
    print("  - Analysis of why non-bijective transformations fail")
    print("  - Information-theoretic interpretation")
    print("  - Shannon (1948) citation")
    print("✓ Inserted after Section 5.2")
    print("✓ Updated subsequent subsection numbering")
    print(f"✓ Notebook saved: {notebook_path}")

    return True

if __name__ == "__main__":
    notebook_path = "../../notebooks/Logic_Realism/12_Unitary_Invariance_Foundations.ipynb"

    success = insert_entropy_bijection_proof(notebook_path)

    if success:
        print("\n[SUCCESS] Notebook 12 enhanced with rigorous entropy→bijectivity proof")
        print("[OK] Addresses team feedback: 'Strengthen analytical proof'")
        print("[OK] Proof is rigorous and complete (Jensen's inequality, strict concavity)")
        print("[OK] Connects to information theory (Shannon 1948)")
    else:
        print("\n[FAILED] Could not insert proof")
        sys.exit(1)
