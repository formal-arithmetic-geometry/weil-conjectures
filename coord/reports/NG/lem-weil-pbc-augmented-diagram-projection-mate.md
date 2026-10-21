# Stage-1 delivery: lem-weil-pbc-augmented-diagram-projection-mate

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-augmented-diagram-projection-mate.json`: statement, split into five steps; no Mathlib match for the whole statement.
- `citations.json`: one verbatim statement extract for each of the fifteen step/node citations.
- `report.md`: this report. `searches.jsonl` is the search command's actual log; `write_split.py` is the sandbox-local JSON-writing script.

New nodes: 0. New Mathlib leaves: 0. No unit record change: this item is not the unit's key statement.

## Attachments

None. The blueprint-id search in `lean/WeilConjectures/` returned no declaration. Searches by projection/mate/tower notions found ordinary monoidal projection maps and normalized adic-system realizations. In particular `NormalizedTowerRealization.lean` constructs maps of normalized systems and their realizations; `LowerStarProjectionBaseChange.lean` concerns the finite-coefficient base-change/projection square. Neither states the general ringed-topos strict derived-tower augmentation equation of this item. No project declaration found gives every clause under the item's hypotheses.

## WANTED

None. The sources needed for this split are available locally.

## Corrections and source route

There was no proof in the item. Its existing dependency list already contains the necessary separate normalizations; this split uses those statements without replacing the item by a restated new node. I corrected the doubled TeX backslashes in the item's statement. The mathematical statement and its hypotheses were not changed. No STATEMENT-DISPUTED issue was found.

I read `literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.md` and its `.proof.md`, including the final coefficient-transition and completion-map clauses, and the current parent node and its `blueprint_update`. The item's generic coefficient-diagram calculation supplies precisely the strict augmentation that the parent's steps 3 and 4 now consume. I also read the fixed chapter and unit records and the main-20261015 proper-base-change unit. This is a lower-level comparison calculation; it changes no unit or chapter route.

The actual projection-map construction is Stacks Tag 0B56, `sites-cohomology.tex`, `equation-projection-formula-map`, in Tag 0943, `section-projection-formula`. I read that construction, Tag 07A4, `lemma-pullback-tensor-product` (including its K-flat representative construction), and Tag 07A6, `lemma-adjoint`. The diagram-site specialization and strict augmentation calculation are expanded here by the worker; accordingly the proof origin is `agent`, not an assertion that Stacks states this entire normalized tower theorem.

## Mathlib and duplicate searches

I ran the authorized `msearch.py` command for LeanFinder, Loogle, LeanSearch, and source grep; the exact queries and actual results are appended to the item and logged in `searches.jsonl`. I tried a second, more general adjunction/counit phrasing in LeanFinder before concluding there was no match. The first broad projection-formula greps returned zero hits. A targeted grep found the ordinary sheaf adjunction/unit API; I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` around line 60, `PullbackFree.lean` around lines 60–100, and `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean` around lines 120–160. They provide underived sheaf adjunctions, unit transposes, and the abstract derived counit, not the full strict-tower result with the specified tensor/evaluation normalizations. LeanSearch's unrelated algebra-tensor hits likewise do not supply it. All services answered successfully in this attempt. The inherited search entries in the original item were retained as inherited records.

Whole-DAG searches used the tags 0943, 0B56, 07A4 and the projection/augmentation/diagram concepts; whole-blueprint searches used `projection mate`, `augmented coefficient`, and `strict tower`. I read the nearby `lem-weil-pbc-ringed-strict-tower-projection-morphism`: it concerns bounded finite-free complex towers and a derived-limit/Roos compatibility, so it does not cover arbitrary commutative algebra-sheaf towers here. Existing `lem-weil-pbc-ringed-projection-mate-exact` supplies the general diagram-site mate used by the proof. No new nodes were needed. The ancestor query confirms `prop-weil-pbc-direct-image-limits`, and `blueprint.same_as` remains empty: no imported blueprint node states this normalized generic refinement.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs.

## Review by NG

I checked the split against delivery-errors B–E with the local sources and all cited node statements open. The key distinction is between a morphism in the derived category of strict diagrams and a family of derived maps. The proof constructs the former by the ringed diagram-site adjunction; evaluation is used only afterward to identify its components. It never infers equality of strict derived-tower arrows from equality after evaluation.

Step 1 uses `lem-weil-pbc-diagram-site-realization` for the exact module equivalence on the small product sites, `lem-weil-tower-category-levelwise-abelian` for exact evaluation, and `lem-weil-pbc-ringed-projection-mate-exact` for the canonical unbounded derived adjunction on those ringed sites. The statement of the first node explicitly allows any small indexing category and small site, so the countable inverse-sequence category is allowed. The componentwise transposition argument is written out to construct the diagram geometric morphism even when the original geometric morphism is not presented by a functor of sites. Termwise exactness uses precisely the hypothesis that module pullback is exact. An exact equivalence and its exact inverse send quasi-isomorphisms to quasi-isomorphisms, which justifies their induced derived equivalence directly from localization.

Step 2 uses the projection node's actual natural transformation, with its first object equal to the constant diagram of K; the reduction node's statement defines B as tensor by the coefficient diagram; the constant-normalization node supplies the displayed chi isomorphism. Thus the construction has exactly the claimed source and target, and its naturality follows from the cited natural maps. There is no requirement that a coefficient sheaf be flat, finite, or perfect: tensors are derived throughout. Unital transitions ensure the ring-to-coefficient augmentation is itself a strict diagram map.

Step 3 uses the reduction node's explicit uniqueness normalization on flat-term K-flat representatives, the projection node's canonical tensor comparison and mate formula, and the constant node's explicit strict counit equation. I checked that these clauses occur in the statements, rather than borrowing their proofs. The equality between the restricted diagram tensor comparison and tau uses the same ordinary pure-tensor comparison and reduction counits on those representatives, exactly as specified in the reduction statement and the construction of Stacks 07A4. The displayed three-line transpose computation then records all comparison maps and their direction. This is a routine substitution of the cited identities, so it is marked elementary relative to those citations, not a new lemma.

Step 4 uses the evaluation-normalization node's actual derived counit equation, not just existence of an evaluation isomorphism. Together with the reduction node's evaluated tensor/pullback comparison and the projection node's counit description, it identifies the evaluated h as an arrow by uniqueness under the ambient adjunction. This checks the potentially delicate normalization: the evaluation adjunction is the specified ambient one, not an arbitrarily isomorphic adjunction. Its hypotheses hold for module sheaves on small sites and their strict diagram categories, which the diagram-site realization again presents as module sheaves on a small site. The exact F required there is explicitly assumed in the item.

Step 5 uses the reduction node's exact augmentation equation and the constant-normalization node's strict counit equation; both are quoted verbatim in `citations.json`. Naturality of i is tensor functoriality for the fixed algebra-unit map and is written explicitly. The two transposes are both the composite of the ambient counit with i_X; the Hom bijection supplied by the diagram-site adjunction proves equality before either evaluation or inverse limit. This is an elementary calculation from existing statements, not a hidden coherence theorem or a relabelled clause delegated to a new node.

For the definition dependencies I read `def-weil-pbc-ringed-topos-morphism`, `def-weil-sheaf-of-modules-category`, and `def-weil-abstract-derived-category`; their notions match the small-site, ringed-topos and localization conventions used. All proof citations are in the same unit, so no off-unit tool declaration is required. I checked that the cited comparison statements introduce their objects and impose no extra constructibility, boundedness, or completeness hypotheses. The source tags were checked in the local tag-to-label table. No SGA source is used.

As small-case checks, with f the identity all counits and comparisons are identities and h is the identity on B. For Q equal to the constant ring diagram, B and i are identities and the asserted equation gives h = chi, as does the construction. For the zero coefficient diagram or K = 0, both transposes vanish. Arbitrary noninvertible transitions remain admissible: no transition map was inverted in the argument. These checks in particular rule out an accidental use of the perfect projection isomorphism. All five proof steps are shorter than 2000 characters; no standalone subclaim with separate hypotheses is hidden in a long step. No new definition, lemma, unsearched Mathlib assertion, or cycle through the parent was introduced.

## Unfinished work

None for this one-level split. The existing comparison nodes may themselves still be open; this delivery does not claim to finish their proofs or to produce Lean. Required server dry run and push are the remaining delivery operations.
