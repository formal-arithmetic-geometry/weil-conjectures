## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-slice-tensor-integer-shift-compatibility.json`: statement node, split into six steps; no exact Mathlib match.
- `citations.json`: verbatim statement excerpts for every step/node citation.
- No new DAG nodes, no Mathlib leaves, no unit-record changes. All statements and maintainer-owned fields are preserved.

## Attachments

None. Searched the project source `lean/WeilConjectures/` for the item id, tensor/shift and restriction/localization terminology. The item tag has no declaration. Read `CategoryTheory/DerivedCategory/Monoidal/ShiftComparison.lean`: `DerivedCategory.commShift_of_tensorLeft_fac` and `DerivedCategory.commShift_of_tensorRight_fac` give general conditional comparison results; they do not themselves assert the normalized slice chain-square formulas or supply all the site's hypotheses and normalization. `AlgebraicGeometry/OpenTensorRestrictionRepresentative.lean` treats an ordinary scheme-open tensor-pullback comparison, not both variables of the unbounded ringed-site derived tensor product here. These are not exact attachments.

## Wanted literature

None. The required sources are present locally; no SGA source is used.

## Findings and corrections

The item was unsplit and had no proof. Its statement is consistent with the source's sign convention, so I kept it unchanged. In particular the second sign is determined by the *unshifted first-factor degree* p, including for negative shifts. The naturality and independence clauses require the two-variable uniqueness statement; choosing one resolution and declaring the answer independent would not prove them.

I reused the already existing derived tensor shift-descent theorem instead of making a node for the item's derived clause. Shifted K-flat admissibility is proved in Step 1 in a few lines from the definition and the cited total shift isomorphism; it is not a new lemma node. Both chain squares are proved by explicit constituent calculations, not by renaming the desired clauses. No statement dispute, route departure or missing hypothesis was found.

The sandbox initially contained no node, report or search log. Copied the live item once, retained its prior Mathlib search records, read their recorded hits, and added the actual newly logged searches. The logged Loogle and grep slice/tensor/shift searches had no hits. LeanSearch found exact-functor shift/localization infrastructure, and the first LeanFinder query found ordinary restriction, free-module pullback, exact-functor shifts and Tor. A second phrasing found good total tensor existence and Tor/flat-module results. The targeted grep and source reads of Mathlib `Algebra/Homology/BifunctorShift.lean` (95-110, 156-174) verify the two chain-shift signs, and `Algebra/Homology/DerivedCategory/ExactFunctor.lean` (80-104) verifies exact-functor factorization shift compatibility. These ingredients already have DAG nodes and do not prove the normalized slice item in one line. Every recorded new query was executed with the supplied msearch command; no unavailable service was recorded as a negative result.

## Blueprint and duplicate searches

Read the chapter and unit records, the current main-20261015 statement and proof of `lemma-weil-pbc-perfect-projection-formula`, and the ancestor computation. This item implements the first proof paragraph's assertion that the comparisons commute with shifts. Its existing precise `blueprint.from.place` and ancestor/via chain are retained. The item is not the unit's key node, so the unit realization is unchanged.

Searched the whole imported blueprint with `blueprint_refs.py` for `tensor shift`, `shift`, `tensor restriction`, `tensor comparisons`, and `slice tensor`, and searched the DAG for integer shifts and restriction/shift terminology. The general total shifts, derived tensor shift descent, exact-functor factorization, normalized slice comparison and tensor descent already exist and are cited. The ancestor's projection formula and its comparison-shift child are broader applications, not duplicate statements of this item. No imported blueprint node states exactly the explicit normalized slice squares and their derived consequence; `same_as` remains empty.

## Not duplicates

No new nodes were created, so there are no new-node/existing-node pairs to distinguish.

## Review by N0

I checked this split against B--E with the sources and the cited statements open. The source for the item is Stacks `more-algebra.tex`, Tag 0FNH, `item-shift-tensor` in `section-sign-rules`: its first shift is unsigned and its second uses the first degree times the second shift. I read the exact item and the shift, tensor restriction, tensor descent, derived shift descent and exact-factorization node statements. I also read `sites-cohomology.tex` Tags 06YS, 06YU and 0G7D, and the statements and representative construction in Tags 0G7E and 07A4. They support the unbounded flat-term K-flat route; they do not state the final signed slice squares, which the worker proves. The proof origin is therefore explicitly agent-written. There are no new nodes requiring separate source reviews.

For Step 1, the K-flat definition states acyclicity against every acyclic first input; `lem-weil-pbc-total-tensor-integer-shifts` supplies precisely the second-variable isomorphism used with E and A. The derived-category definition gives the shift differential. Reindexing kernels/images checks the shifted acyclicity, and flatness of shifted terms is just reindexing. This also avoids assuming that flat terms alone imply K-flatness.

For Step 2, `lem-pc-kflat-resolution` provides resolutions with flat terms for arbitrary complexes, not merely bounded ones. `lem-weil-pbc-site-derived-tensor-descent` gives the canonical model isomorphisms. `lem-weil-pbc-ringed-slice-evaluation-transpose` explicitly says that slice restriction preserves these resolving complexes and that rho is represented by the stated m. I use only that tensor-model clause; I do not infer anything from its internal-Hom or evaluation proof. `def-pur-localized-ringed-site` states that restricted module maps have their original section maps, and `lem-sfb-localized-site-tensor-restriction` explicitly asserts naturality in both sheaves. Its stated pure-tensor formula agrees with the normalization, giving the summand equation displayed in Step 2.

For Steps 3 and 4, the total shift theorem supplies the exact signs and direction, and the slice normalization supplies the component mu. First-variable source degree p corresponds to A^(p+n); the target component is (p+n,q). In the second-variable square the component is (p,q+n), and the first degree remains p, so the sign is (-1)^(np) on both routes. Restriction preserves additive inverses by its sectionwise definition, and a module map commutes with multiplication by either sign. Coproduct uniqueness proves equality as sheaf maps in each degree; I do not claim that arbitrary sections of a sheaf tensor product are globally sums of pure tensors. Both composites are already chain maps by the cited isomorphism statements. No differential-compatibility lemma is hidden here.

For Step 5, I checked that `lem-weil-pbc-derived-tensor-shift-descent` actually asserts existence and naturality with the *published tensor-model normalization*. It is applied over both rings, with shift stability verified in Step 1. `def-weil-pbc-ringed-derived-restriction` defines the functor by exact additive restriction. The exact-functor factorization node explicitly asserts that its factorization isomorphism commutes with shifts, so this is a theorem citation, not a fact inferred from a definition. The normalization and tensor-descent statements identify rho and all the tensor models. These are precisely the isomorphisms used when the chain identities are localized, so the intermediate factors cancel and the equality obtained is the one asserted, not an equality for an arbitrarily chosen comparison.

For Step 6, I opened `lem-weil-pbc-site-derived-tensor-descent` and checked its final sentence: it concerns *arbitrary natural transformations of two bifunctors*, not merely naturality of the tensor bifunctor itself. Taking E to be D(O_W) and U,V as displayed in Step 5 therefore satisfies its conclusion literally. The site and slice are small relative to the module universe (the slice of a small site is small), so this is the published resolving equivalence in the correct universe. Both transformations are natural by the normalized comparison and derived shift statements; uniqueness proves equality and compatibility with changes of representatives, inverted quasi-isomorphisms, and any normalized tensor presentation. No boundedness, perfectness, enough points, projective terms or extra finite-size assumption was used.

I tested n=0 (both squares reduce to the same m), positive and negative odd n with p odd (both second-variable routes are -mu), even p or even n (both are mu), the zero input, and characteristic two (all signs coincide). Unbounded complexes cause no new issue: the sums in each degree are those already supplied by total tensor and m, and the equality is tested constituent by constituent. All six steps are shorter than 2000 characters. The only off-unit statement tools are the normalized slice tensor comparison and the natural ordinary tensor restriction isomorphism, declared with reasons in split_report.tool_uses; no unit route is replaced.

The citation excerpts are literal substrings of the current cited statements, checked for every cited node and read against the mathematical use. The proof dependency list is exactly the union of all step uses; inspected dependencies do not lead back to the item. No new statement-only node contains a hidden proof because no new nodes are delivered.

## Unfinished work

None in the stage-1 split. Server dry-run and delivery results are recorded by the delivery tool. This report claims a natural-language split, not a Lean proof or a new attachment. No Lean was written and no compiler or build tool was run.
