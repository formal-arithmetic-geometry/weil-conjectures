# Stage-1 report: lem-trf-derived-basis-limit-extension

Group Q79; 2026-10-23. Direct delivery.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-derived-basis-limit-extension.json`: statement, split using two existing same-unit inputs; not a Mathlib leaf. Statement, ancestry, source, creation record and earlier searches retained.
- `citations.json`: exact statement quotations for every cited node in every proof step.
- `report.md` and `searches.jsonl`: report and actual search-command evidence.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and for derived-basis, increasing-union, ordinal-gluing and negative-self-extension notions. No project declaration states the item. Existing two-open gluing results cannot cover this item and were not offered as attachments. Existing `Sheaf` statements are not treated as completed upstream proofs.

## WANTED

None. The source used is available in `literature/stacks-project/cohomology.tex`.

## Findings and changes

The imported item was statement-only. Its assertion is sound as written: the family called a basis need only cover and refine pairwise intersections; it need not be a basis for the entire original topology. In particular one cannot assume that an arbitrary open subset is a union of its members, or that a member of the family is contained in one earlier stage. The proof explicitly constructs the required stage-refining collections instead. No statement dispute or correction is needed.

I read Stacks 0D6B (`cohomology-lemma-glueing-increasing-union`) and the limit and final paragraphs of 0D6C (`cohomology-theorem-glueing-bbd-general`), as well as 0D66 and 0D68 (`cohomology-lemma-vanishing-and-glueing` and `cohomology-lemma-uniqueness`). The two printed slips inside the proof of 0D6B (reference to finite-case existence in place of uniqueness, and the direction of its comparison) are already addressed by the existing increasing-union node; this delivery uses its statement, not those slips. The final paragraph of 0D6C omits compatibility checks; Steps 2, 4 and 5 supply the formulas and equalities.

Read the chapter and unit records, the three-level rules in SETUP, and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/` unit and local-term proof. The current local-term proof uses contracting correspondences and does not itself state this general derived gluing lemma. The item's existing BBD-support ancestry is retained. This split is below the unit and introduces no replacement of its route, chapter change, unit change, or off-unit tool citation.

## Searches and reuse

Whole-DAG tag searches 0D6B, 0D6C and 0D68, together with the derived-basis family, locate the existing increasing-union, local-Hom, binary-extension and BBD-descent nodes. Read their statements and the existing increasing-union/local-Hom splits. The latter two are already split and reviewed and suffice; the BBD theorem depends on the item and is deliberately not cited. The binary-extension lemma does not supply this limit argument.

Whole-blueprint searches through `tools/blueprint_refs.py` for `glueing`, `negative`, `derived gluing`, and `continuous ordinal` yield no blueprint node stating this item; `same_as` stays empty. The ancestor command confirms `lem-trf-local-term-locality`. No node is created, so there is no new-node duplicate pair.

Read all six fresh msearch results and retained the prior searches. The first LeanFinder phrasing found bounded representatives, fractions and injective dimension. The second found fraction presentations and representatives. LeanSearch found ordinary presheaf/topological gluing. Loogle `DerivedCategory, "glue"` and targeted greps in Algebra and AlgebraicGeometry returned no hits. Inspected `Mathlib/Topology/Sheaves/SheafCondition/UniqueGluing.lean` (IsGluing at 66, IsSheafUniqueGluing at 77), `Algebra/Homology/DerivedCategory/Fractions.lean` (right_fac 45, left_fac 59 and bounded variants), and `DerivedCategory/TStructure.lean` (exists_iso_Q_obj_of_isGE_of_isLE at 180). None supplies the effectivity or local negative-Ext hypotheses needed here. All fresh queries are recorded exactly as run with their actual digests, and all services answered.

## Not duplicates

No new nodes. Reused `lem-trf-derived-basis-increasing-union` for object effectivity and `lem-trf-derived-basis-local-hom-glue` for Hom bijections, without restating either.

## Review by Q79

I checked B through E of delivery-errors against the item, the sources and the full statements of both cited nodes. There are no new statement-only nodes to audit. The source tags and labels were checked against `literature/stacks-project/tags/tags`. Every proof step is shorter than 2000 characters; no auxiliary comparison theorem or construction is hidden in a long step.

Step 1 uses exactly the increasing-union node's conclusion: an object on the union and coherent comparison isomorphisms. On the open subscheme W_lambda its hypotheses are the supplied set-sized ordinal, covering equation, monotonicity, continuity including the empty initial open, negative self Hom and cocycle. It does not need any basis maps or quasi-compactness. I read the cited node's full statement and checked all these hypotheses individually.

Step 2 is elementary from the data. To cover a point of U, choose a stage, then a family member inside that stage through the point, and refine its intersection with U. This is valid because each stage is a union of original family members. The same intersection-refinement property proves the new collection refines intersections. For a member contained in two stages, ordinal comparability and the two supplied comparison equations give the identical local map. For a smaller member, both can be evaluated in the stage of the larger one; the rho cocycle and the earlier solution equation give compatibility. No unproved assertion about a true topological basis is used.

Step 3 uses the local-Hom node's stated bijection on the scheme U, with O=U and the specific covering collection from Step 2. Its negative cross-Hom hypothesis holds since both objects on each member V are isomorphic to K_V. Conjugation by these isomorphisms, including shifting the target isomorphism, reduces it to the item's supplied negative self-Hom vanishing. This also checks the reversed pair and the two self pairs, needed to glue inverse maps and identify both composites with identities. The bijection supplies the map and uniqueness, and its injectivity supplies invertibility by this explicit inverse argument; the citation is not being used for an unstated theorem that local isomorphisms automatically glue.

Step 4 applies that same stated Hom injectivity on T with the stage-refining collection for T. Both maps have the same source and target. I wrote the restriction of their composite and used rho_V^U = rho_V^T composed with rho_T^U restricted to V to simplify it to the second map's local formula. The negative cross-Hom check is again exactly conjugation to K_V. This proves the entire solution equation even when U or T is contained in no single earlier stage.

Step 5 takes V=U when U lies in a stage, so rho_U^U=1 yields the required stage identification directly, without another descent argument. Comparison coherence is already part of Step 1. The cited local-Hom statement explicitly covers empty schemes and empty collections: therefore the identity/inverse and uniqueness arguments in Step 3 work unchanged if U is empty, if the family contains the empty open, or if all stages are empty. Repeated stages and repeated opens cause no ambiguity by the stage-independence calculation. The first possible nonzero limit lambda=omega satisfies all the same arguments, and nothing assumes countable cofinality for larger limits.

I checked the dependency direction: neither cited input depends on this item; both are same-unit tools already present. The union of step citations is exactly proof_deps. All citations.json quotations are verbatim substrings of those statements and describe the Hom bijection or the full coherent-gluing conclusion actually used. The item remains set-sized, unbounded, with the original coefficient category of O-module sheaves and without added hypotheses.

## Unfinished work

None in the mathematical split. Required remote dry run and push follow this review; their outcome is recorded by the delivery tool.
