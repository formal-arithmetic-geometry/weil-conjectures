Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-generic-vanishing-acyclic.json` — statement, 4 proof steps, 3 proof dependencies, and split report.
- `dag/nodes/sec-curve-estimates/lem-sc-generic-vanishing-kernel-colimit.json` — new unsplit statement; Mathlib searches found no match.

Attachments:

- `AlgebraicGeometry.IsCurve.subsingleton_H_of_genericVanishing` belongs to `lem-sc-generic-vanishing-acyclic`; it is present at `WeilConjectures/AlgebraicGeometry/Curve/GenericComparison.lean:140-232`, but its sorry map is `rests_on_sorry` through `Scheme.H_map_isColimit_of_isFiltered`, so this is not an attachment as a finished node.

WANTED:

- None. The cited Stacks and blueprint sources are present in the project literature index; the Lean construction is read directly from `GenericComparison.lean`.

What was wrong or incomplete:

- The imported item had no proof split and its `created` record was incomplete. I added the missing split metadata and made the proof route explicit.
- The Lean theorem's no-torsion hypothesis is essential to this item's distinction from `lem-sc-zero-generic-acyclic`; I retained it exactly and did not cite the torsion-only node as a substitute.
- The new kernel-colimit node is intentionally unsplit because it packages the central construction in the Lean proof and is not a Mathlib theorem.

What could not be finished:

- No Lean code is written at stage 1. The tagged declaration remains transitively sorry-dependent and therefore cannot close this node.

## Review by C1

I read the item's source in the master blueprint and the exact tagged Lean theorem and docstring in `GenericComparison.lean:140-232`. The theorem uses the sieve condition `hG`, builds the filtered diagram of kernels of the affine-open units, proves its colimit map is mono and locally surjective, proves each kernel has zero restriction to the chosen affine open, and then uses cohomology of filtered colimits. I made the new node state precisely the first construction, including its transition maps and the covering hypothesis; I checked that its objects and maps are the same `K`, `Dg`, `cG`, and `phi` defined in lines 164-211.

For step 1 of the item I cited that new node because the colimit construction and the mono/locally-surjective argument are non-elementary and are not in Mathlib. For step 2 I read the finite-support acyclicity statement and checked the Lean argument: pulling back the unit gives an isomorphism by the adjunction triangle identity, while an affine open in an integral curve has finite closed complement with separably closed residue fields; this matches `lem-sc-finite-support-acyclic`. For step 3 I read the existing filtered-colimit cohomology node and Stacks Tag 03Q5, and verified that an integral finite-type curve is quasi-compact and separated, hence quasi-separated. Step 4 is only the zero colimit calculation, so I marked it elementary. I searched the DAG and blueprint before creating the kernel-colimit node and found no duplicate; its LeanSearch, Loogle, and Mathlib-source grep records all report no matching theorem. I also checked the edge case that a nonzero constant sheaf does not satisfy the generic-vanishing sieve condition, so the hypothesis is substantive. The only correction was filling the previously empty proof and creation metadata while preserving the original statement and dependencies.
