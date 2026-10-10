# Delivery report

1. Files written:
   - `dag/nodes/sec-curve-estimates/lem-sc-noetherian-topological-cohomology-vanishing.json`: repaired item with the 02UZ outer and inner inductions.
   - `lem-sc-noetherian-open-closed-cohomology-sequence.json`: unsplit statement-only node, no Mathlib match.
   - `lem-sc-irreducible-noetherian-constant-acyclic.json`: unsplit statement-only node, no Mathlib match.
   - `lem-sc-noetherian-extension-by-zero-reduction.json`: unsplit statement-only node stating Stacks 02UX exactly.
   - `lem-sc-noetherian-finite-irreducible-components.json`: Mathlib leaf matching `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`.
   - `citations.json`.
2. Attachments: none. No exact sorry-free Lean declaration for the item was found.
3. WANTED: none; the cited Stacks tags are present in the project literature.
4. The returned conditional reduction node was replaced by the four-hypothesis implication of 02UX. The short exact sequence for `Z_U` is now derived in the item from the open-closed sequence applied to the constant sheaf `Z_X`. The finite-components node is a Mathlib leaf and no longer contains a proof method. The item’s d=0 irreducible case now explains why every sheaf is constant before applying constant-sheaf acyclicity.
5. Nothing remains unfinished.

## Review by G1

I reread the item and all four new nodes, the blueprint ancestor, and the Stacks source for Lemmas 0052, 02UT, 02UW, 02UX and Proposition 02UZ. Step 1 uses only the cohomology definition for the empty-space base case. Step 2 uses the exact finite-components statement, the open-closed short exact sequence, and its stated long exact cohomology consequence. Step 3 checks the dimension-zero irreducible argument and then checks 02UX hypotheses (1)-(3) from Noetherian quasi-compactness; the cited constant-acyclic and 02UX statements say exactly those facts. Step 4 handles both open cases, verifies that the complement is proper Noetherian of dimension at most d-1, and uses the open-closed sequence with `F=Z_X`, closed-immersion cohomology comparison, constant-sheaf acyclicity, the outer induction, and the long exact sequence. Step 5 applies the exact 02UX conclusion and closes both inductions. I verified every citation quote against the current node statements, including the extension-by-zero and constant-sheaf definitions, and corrected the previous report’s deleted conditional/generic-point description.
