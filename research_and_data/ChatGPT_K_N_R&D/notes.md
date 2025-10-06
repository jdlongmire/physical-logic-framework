Notes and next steps for K(N) R&D

- Current plan:
  1. Run enumeration up to N=10 to observe whether K(N)=N-2 matches the selection rule used in the paper for small N.
  2. If candidate matches small N, attempt to search for combinatorial/graph interpretations (e.g., distance in Cayley graph under adjacent transpositions) that could justify K(N)=N-2.
  3. Use multi-LLM pipeline to propose Lean lemmas and proof skeletons.

- TODOs:
  - [ ] Run the enumeration script and save `results_N_1_10.csv`.
  - [ ] Inspect `research_and_data/K_DERIVATION_SYNTHESIS.md` for any definitions of K(N).
  - [ ] Run the multi-LLM consultant on the question: "Is there a combinatorial reason K(N)=N-2?" and collect suggested proof approaches.

## Enumeration summary
- Script `enumerate_kn.py` run with K(N)=N-2 for N=1..10. Results in `results_N_1_10.csv`.
- Observations:
  - K(3)=1 and K(4)=2 match the paper's verified small-N cases.
  - Fraction of permutations retained by the cutoff drops quickly (from 0.5 at N=3 to ~0.0046 at N=10).

## Next concrete steps
1. Search for the formal definition of "valid" in paper/ and lean/ docs (`research_and_data/K_DERIVATION_SYNTHESIS.md`, `lean/*`) to verify that the operational selection equals the simple h(σ) ≤ K cutoff.
2. If the repo's definition matches this inversion-count cutoff, attempt to (a) compute K(N) from first principles, or (b) use multi-LLM to generate a Lean lemma scaffold.
3. Produce plots (Mahonian distribution + cumulative up to K) to visualize the selection.
4. Start drafting a Lean lemma for small-N induction or a combinatorial bound; use multi-LLM to propose proofs and then attempt Lean translation.

