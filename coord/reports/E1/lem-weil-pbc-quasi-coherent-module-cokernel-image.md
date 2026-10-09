# Stage 1 report: lem-weil-pbc-quasi-coherent-module-cokernel-image

Repaired the returned split on current `origin/sheaf-dag`.

- Added a self-contained `lem-weil-pbc-sheaf-cokernel-local-image` statement with explicit sheafification/module definitions, exact Stacks tag 01AH, and the required LeanSearch/Loogle/grep searches.
- Removed the non-leaf `lem-weil-pbc-quasi-coherent-affine-cokernel-calculation` node.
- Rewrote the affine step to use the existing `lem-weil-pbc-affine-tilde-gamma-adjunction` clauses (2), (3), and (4), avoiding any false claim about arbitrary open sections; the quotient formula is obtained on the chosen affine $U$ via its global sections.
- Made Step 1 state that restriction preserves cokernels by clause (1) of `lem-weil-pbc-module-restriction-open-immersion-colimits`, and preserves quasi-coherence by clause (2) together with the affine-local criterion `pqf-def-coherent`.
- Added exact Stacks tags 01AJ, 01BG, 01IC, 01IB, 01I7, 01LB, and 01AH to the relevant proof steps and source fields.

Checks:

`python3 tools/review_split.py lem-weil-pbc-quasi-coherent-module-cokernel-image` passes. `python3 tools/check_dag.py` reports only the seven pre-existing reach warnings and no cycles or missing dependencies.

## Review by E1

I checked the repaired split against Stacks 01AJ, 01BG, 01IC, 01IB, 01I7, 01LB, and 01AH and against the cited DAG nodes. Step 1 now explicitly uses the restriction colimit clause and affine-local quasi-coherence; Step 2 reuses the reviewed affine tilde/Gamma node instead of claiming a standalone Mathlib leaf; and the quotient formula is stated only on affine opens. The local-image child is self-contained, statement-only, and has its own three search records and exact 01AH source. All four return reasons are addressed, the route remains `sk-thm-p1`, and the delivery is one item-only commit from the current base. I accept this repair.
