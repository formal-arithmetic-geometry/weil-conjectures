# lem-weil-pbc-property-implies-acyclicity

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-property-implies-acyclicity.json`: split the PBC-to-IA implication into five cited steps; no new DAG nodes were needed. Mathlib verdict: no match after LeanSearch, Loogle, LeanFinder, and Mathlib-source grep.

## Attachments

- `AlgebraicGeometry.Etale.HasTorsionBaseChange.hasInjectiveAcyclicity` is related but does not belong to this node: its statement is for sheaves of modules over an arbitrary coefficient ring, while this node states PBC for torsion abelian sheaves and IA for every prime field; the coefficient-forgetting comparison is not part of that declaration.

## WANTED

WANTED: none.

## What was wrong or incomplete

The imported item had no proof steps. I made the source's forward implication explicit: specialize PBC to the torsion injective sheaf in degree zero; use the existing module-to-abelian direct-image acyclicity statement and the degree-zero derived identification; preserve the vanishing under exact inverse image; transfer it across the specified exchange isomorphism; and quantify over all primes and base changes. I removed the earlier top-level `tool_uses` field and declared the two off-unit generic tools in `split_report.tool_uses`, as required. The source Lean theorem was checked against the item and deliberately not attached because it quantifies over arbitrary coefficient rings and module-valued IA, whereas this node states the prime-field torsion abelian formulation.

## What could not be finished

No Lean was written or compiled, as required for stage 1. The item remains a split DAG statement pending lead review.

## Review by M1

I read Stacks Tag 0A4B (Lemma 59.91.6), including the statement that PBC implies vanishing for every prime-field injective sheaf and the proof's degree-zero specialization, and compared it with the source docstring at `BaseChangeProperty.lean` lines 198–205. The item statement has the same proper morphism, arbitrary cartesian base change, prime $r$, injective $\\mathbf F_r$-module sheaf, and $q>0$ vanishing hypotheses and conclusion. Step 1 cites the PBC, cartesian-square, derived-exchange, and etale-sheaf statements, which together provide exactly the torsion degree-zero test object and specified isomorphism. Step 2 cites the direct-image definition, the existing module-injective acyclicity theorem, and the left-exact injective-resolution degree-zero theorem; these give the source's vanishing in positive degrees and its degree-zero identification. Step 3 cites exact inverse image and exact-functor cohomology, then the exchange and direct-image definitions; this is the source's transport of concentration and identifies the target cohomology with $R^qf'_*g'^{-1}I$. Step 4 is the elementary universal quantification over the arbitrary square, prime, and injective. I checked every cited id exists and that the two generic off-unit facts are declared as `split_report.tool_uses`. The item has no new nodes, so there are no additional Mathlib leaves or statements to test; the Mathlib searches recorded in the item found no etale proper-base-change theorem. I corrected the prior attempt's stale Stacks places to Tag 0A4B labels, removed its forbidden top-level tool-use field, and retained the related Lean declaration only as an attachment note because its coefficient quantification is not exact.
