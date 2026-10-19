# Stage-1 report: lem-pur-integral-coherence-tower

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-integral-coherence-tower.json`: statement node, split; no new Mathlib leaf.
- `citations.json`: verbatim statement excerpts for every proof-step citation.
- `searches.jsonl`: three Mathlib searches run for this item.

## Attachments

None. No finished declaration with this item’s exact statement was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `/home/ubuntu/weil-newtargets-master/WeilConjectures`.

## WANTED

None.

## Source or item issues

The imported item had an empty proof. Its statement is well-typed as a chain-level/tower-level assertion under the listed quotient, K-flat, pullback, and normalized-tower conventions. I did not change the statement or its statement dependencies. No new node was created: the only extracted supporting fact needed for the normalizedness check is the existing `lem-pur-system-normalized-tensor-closure`, used as a declared generic tool lemma because its unit is outside this conventions unit.

## Review by Q117

I read the complete item node, the `sk-def-purity-conv` unit, the `sec-smooth-purity` chapter record, and the source locations named by the item (`sites-cohomology.tex`, Tags 07A4 and 0941). I also read the complete statements of every node cited in the six proof steps, including the existing normalized tensor/pullback closure tool, and checked each citation against `citations.json` verbatim.

Step 1 checks the hypotheses on the coefficient rings and quotient maps from `def-weil-completed-integral-coefficients`, the K-flat and flat-term assumptions from `def-pc-kflat-complex` and `def-pc-flat-sheaf-modules`, the direct-sum total construction from `def-pc-tensor-complex-sheaves`, and termwise pullback from `def-weil-proetale-inverse-image`. The actual transitions are the quotient maps, and their adjoints are the canonical tensor-association maps; the existing `lem-pur-system-normalized-tensor-closure` states the needed normalized tensor and pullback transition formulas. I checked the unit tower as the same construction with the coefficient ring itself.

Steps 2 and 3 use exactly the cochain comparison statement: its pure-tensor map and inverse, reassociation compatibility, Koszul signed symmetry, action unitors, pullback composition comparison, and coefficient-square compatibility. I checked that the displayed composition equation has the same orientation and the canonical `a_K` as the item, and that the unit identification is the pullback of the quotient coefficient sheaf. The direct-sum differential and the signs are those of `def-pc-tensor-complex-sheaves`.

Step 4 uses the cochain lemma’s explicit final clause that all formulas on strict quotient towers commute with transitions. Thus the maps and inverses in Steps 2–3 are strict tower maps, rather than merely levelwise maps. I verified that this supplies every transition compatibility requested by the item and does not use a finite-level faithfulness claim.

Step 5 applies the functorial derived-limit assertion of `lem-weil-pbc-ringed-strict-tower-homotopy-limit`. I read the substitution statement in full and checked that it identifies limits of tensor, pullback, reassociator, unitor, signed symmetry, and composition maps with the corresponding completed integral operations. Equality and inverse identities therefore survive the limit.

Step 6 applies the normalized-tower effectivity comparison and the substitution counits. I checked that the resulting reduction isomorphisms are coherent for every `m≥n`, so the reductions recover the finite equations together with quotient-transition maps. Edge cases checked in the argument are `n=1`, `m=n` (identity transition), `f=id` and `h=id` (identity composition comparisons), the unit complexes, and homogeneous degrees `p=q=0` (sign `+1`); the formulas reduce to the expected identity maps in each case.

The three Mathlib searches (LeanFinder, Loogle, and Mathlib grep) returned only generic normalization or homological declarations and no statement of this sheaf quotient-tower construction; their exact queries and outcomes are recorded in `searches.jsonl` and in the node’s `mathlib_searches`.
