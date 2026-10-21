# Q44: lem-kun-kflat-short-exact-quotient

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-kflat-short-exact-quotient.json`: statement, now split into five steps; not a Mathlib leaf. The statement and its six statement dependencies are unchanged. Preserved all inherited fields and Q105 searches, and appended the actual Q44 searches from `searches.jsonl`.
- `citations.json`: seven entries covering every cited node in every proof step, each checked as a literal substring of the cited statement.
- `report.md`: this report. `write_split.py` is a sandbox-only writing helper, not a delivery node.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None for the item. Read-only searches in `lean/WeilConjectures/` found no blueprint tag for this item and no declaration covering both its total-tensor exactness and flat-quotient K-flatness assertions. The project has generic K-flat results in `FromJoel/CategoryTheory/Abelian/Flat/KFlat.lean`, but its triangulated closure result does not state degreewise total-tensor exactness for a degreewise nonsplit sequence. Ordinary ring-module flatness results do not constitute a sheaf-complex attachment.

## WANTED

None. All sources used are present in the read clone.

## What was wrong or incomplete

The item was a valid but unsplit statement. Its proof and proof dependencies were empty. The total-tensor exactness sentence in the proof of Stacks 0G7B hides exactness of an infinite direct sum of sheaf sequences; the split supplies that argument using finite subsums and exact filtered colimits. It also handles explicitly the order of tensor factors: the item's displayed sequence has the test complex on the right, whereas the existing K-flat definition has the acyclic test complex on the left. No statement correction or route departure was needed.

The blueprint ancestor is `lem-kun-0f1m`, as confirmed by `tools/blueprint_refs.py ancestor`. Its stored source proof uses the flat-quotient short exact sequence in the amplitude-to-model argument. The main-20261015 version has the same statement but no proof text. The current DAG parent and Stacks 0F1M identify precisely the 0G7B input. Filled the item's `blueprint.from.place` accordingly and retained `same_as: []` after blueprint searches for K-flatness, 0G7B and flat quotient. Whole-DAG tag searches found only this item, its parent and the already existing sheaf-level flat-quotient theorem.

## Mathlib searches

Ran the prescribed Q44 `msearch.py` commands for LeanFinder, Loogle, grep and LeanSearch, then a second semantic phrasing and a more targeted grep. Actual queries and returned names are appended to the item and recorded by the search tool in `searches.jsonl`; there are no invented searches. Both semantic phrasings returned ordinary-module flat tensor exactness. Read `Mathlib/RingTheory/Flat/CategoryTheory.lean:41-48`: these declarations assume the fixed tensor factor is flat and concern `ModuleCat`, so neither is the full flat-quotient sheaf-complex assertion. The second search also returned `LinearMap.lTensor_injective_of_exact_of_flat`, again an ordinary-module component result rather than the whole item. No match or unavailable service was silently reclassified.

## Not duplicates

No new nodes. Reused `lem-weil-pbc-site-flat-quotient-tensor-ses` for the 03EX input, `lem-pur-ringed-site-grothendieck-abelian` for the 03DB colimit input, and `lem-weil-pbc-complex-ses-homology-long-exact` for 0117. Finite biproduct exactness and the finite-subsum description of a coproduct are proved inline rather than made into redundant nodes.

## Review by Q44

I read the item against Stacks `sites-cohomology.tex`, Tag 0G7B, label `lemma-K-flat-two-out-of-three-ses`, including the entire proof. I also read the actual sheaf assertion (2) of `sites-modules.tex`, Tag 03EX, label `lemma-flat-tor-zero`; Tag 03DB, label `lemma-limits-colimits`; and `homology.tex`, Tag 0117, label `lemma-long-exact-sequence-cochain`. These give exactly the source route: termwise tensor exactness, totalization, and the long exact cohomology sequence. No SGA source is used. No new-node source review is needed because no new node was created.

Step 1 uses the statement of `lem-weil-pbc-site-flat-quotient-tensor-ses`, which explicitly gives short exactness after tensoring with any sheaf when the quotient is flat. I checked the small-site, commutative-ring and degreewise short-exact hypotheses against the item. The flat object is the quotient P^p, not the arbitrary test term A^q. The node's additional flat-kernel conclusion is unused.

Step 2 uses the presheaf tensor and sheafification construction stated in `def-pur-sheaf-tensor-product`. I wrote the inverse maps on pure tensors and checked their compatibility with restrictions and both sequence maps. This is the elementary tensor symmetry calculation, and only serves to obtain a termwise sequence with A on the left. It does not require a hidden comparison between total complexes or an unmentioned Koszul-sign isomorphism.

Step 3 uses exactly the small-colimit and exact-filtered-colimit clauses of `lem-pur-ringed-site-grothendieck-abelian`. The site in that node is small and the coefficient sheaf is commutative, as required here. For fixed total degree n, the indexing set is a subset of Z squared in the sheaf universe. Its finite subsets form a small filtered poset with union as upper bound. Finite biproduct exactness is justified directly by the kernel and cokernel universal properties, and the identification of the colimit with the full coproduct is justified by its universal property. Thus the cited node supplies the only non-elementary operation in this step. In particular the argument never assumes that an epimorphism of sheaves is surjective on sections, and never replaces a coproduct by a product.

Step 4 reads off the total terms and differential from `def-pc-tensor-complex-sheaves`, which states their formulas and functoriality. I checked commutation with the first and second differential separately for f and g and for both tensor orders. The map has degree zero, so it preserves the sign belonging to the fixed summand. Each summand has two outgoing differential components, regardless of the number of summands in a degree. This is the elementary chain-map verification, not an extra unproved totalization-exactness assertion.

Step 5 uses the full long exact sequence stated by `lem-weil-pbc-complex-ses-homology-long-exact`, which permits integer indexing and any abelian category. The module category is abelian by the step-3 node. I wrote the three exact segments separately so that all choices of the missing K-flat complex are covered, including the degree shift in the case where L is missing. `def-pc-acyclic-complex-modules` supplies the cohomological vanishing criterion, and `def-pc-kflat-complex` supplies exactly the universal quantification over acyclic test complexes on the left. Every quoted node statement was opened and read, and `citations.json` contains the actual portion used.

I tested the zero complex and zero coefficient sheaf, the identity sequences with zero left or right term, and complexes concentrated in one degree. In the latter case the first assertion reduces to the sheaf flat-quotient tensor lemma. The excluded flatness-free claim fails already for 0 → Z --2→ Z → Z/2 → 0 tensored with Z/2; this confirms why step 1 must use quotient flatness. The filtered-finite-subsum argument works for infinitely many nonzero summands and supplies the unbounded case without a boundedness or degreewise splitting assumption. All cited dependency closures were checked not to reach the item, so the split introduces no cycle.

Checked delivery-errors B–E: no new unsplit nodes with hidden proofs, no undeclared notions, no duplicate or clause-restatement nodes, no unavailable searches presented as failures, and no claim taken merely from another node's proof. The two other-unit tools are declared in `split_report.tool_uses` with their precise roles; they are generic inputs to the stated Stacks argument. All five proof steps are below 2000 characters, and none conceals a source's omitted lemma.

## Unfinished work

None in this stage-1 split. The existing supporting nodes keep their own states; this delivery makes no claim that their Lean proofs are closed.
