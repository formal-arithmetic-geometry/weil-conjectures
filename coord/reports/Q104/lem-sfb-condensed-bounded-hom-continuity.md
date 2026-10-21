## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-condensed-bounded-hom-continuity.json`: split statement; unchanged mathematical statement; four proof steps; no Mathlib match.
- `citations.json`: eight entries, one for every step/node citation, copied verbatim from the cited statements.
- `searches.jsonl`: five actual searches recorded by msearch.py. Existing item searches from Q62 are retained in the node; new distinct searches are appended.

No new nodes and no Mathlib leaves. The item is not its unit's key statement, so no unit record is changed.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for constructible/colimit and Hom/Ext-continuity concepts. `ModuleObject/Derived/CompactConstructible.lean:134` defines `HasConstructibleExtContinuity`; it is a predicate for factorization of sheaf-to-sheaf maps, not the theorem here. `ModuleObject/Derived/CompactConstructibleEllAdic.lean:72` states `hasConstructibleExtContinuity_continuousMapRingObj`, but its proof is `sorry`, its geometry is separated finite type over a field, and its conclusion is that weaker predicate. `ModuleObject/Colimit/TwoColimit.lean` describes the needed continuity in its module docstring as sorried input, not as a finished declaration. These are not attachments.

## WANTED

None. The blueprint and the relevant Stacks source are present.

## Corrections and scope

The inherited item had an empty proof. Its statement, statement dependencies, source, created metadata, chapter, unit and precise blueprint.from place are preserved. I filled in the finite cohomology-cone induction and explicitly identified the canonical comparison map. No statement dispute or change of route is needed.

I did not cite `sk-lem-constructible-ext-continuity` for the whole item: its statement assumes locally Noetherian and quasi-compact, whereas this item assumes only that the underlying topological space is Noetherian. Its constructible-generation specialization also uses finite constant local models, rather than the locally finitely presented predicate used here. I instead cite the existing exact sheaf-level base case, `lem-weil-pbc-condensed-sheaf-ext-continuity`, which has the correct geometry and coefficient predicate. For `det-lem-constructible-ext-continuity-devissage` I use only its general first part, which is valid on any scheme. Its final specialization with stronger geometric hypotheses is not used.

The three non-elementary tools are declared in split_report.tool_uses: the matching sheaf-continuity base case, formal stability of the comparison property, and the finite bounded-cohomology cone witness. They implement the unit's sheaf-to-complex continuity step, without changing the coefficient-descent argument. The chapter and unit route are preserved.

## Not duplicates

There are no new nodes or same-tag pairs to justify. Whole-DAG statement searches found the three needed ingredients already present. Whole-blueprint searches for `constructible ext continuity`, `devissage`, `bounded cohomology`, `Hom continuity`, and `truncation`, together with the current continuity node statements, found no blueprint statement identical to the item with its precise hypotheses. The locally Noetherian continuity theorem is more restrictive and does not cover this item. Thus blueprint.same_as remains empty.

## Mathlib searches

I ran the required msearch commands for the item with LeanFinder, Loogle, grep and LeanSearch, and tried a second LeanFinder formulation about closure along finite Postnikov towers. All five services returned successful responses. The hits concern AB5/AB4 and colimits of condensed modules, colimits of complexes, or support conditions in the standard derived t-structure. None states the item's theorem. The grep hit at Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean:346 is inside `Ext.biprod_ext`; I read the surrounding declaration and it concerns binary biproducts, not filtered constructible continuity. The second formulation returned `DerivedCategory.IsGE`, `IsLE`, `TStructure.t`, and related support facts, not this Hom comparison. Queries and actual returned names are recorded without inventing an unavailable service or an exact match.

## Review by Q104

I read coord/brief-stage1.md, stages/1-dag.md, the three fixed/followed/free levels in SETUP.md, GOAL.md, the worker role, the chapter and unit records, and delivery-errors B through E. The item's source is paragraph 2 of `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/lem-sfb-constructible-cocone-hom-surj.proof.md`. It asserts the sheaf base case and extension to K by five lemma. The unit's part (2) uses precisely continuity into uniformly bounded-below complexes. I read the complete statements of every cited node. No new node needs an additional source review.

For step 1, the first part of `det-lem-constructible-ext-continuity-devissage` defines exactly the comparison into the termwise colimit and states closure under shifts, isomorphisms and extensions. It explicitly says no common lower bound is needed for that formal assertion and puts no Noetherian assumption on its first paragraph. `def-weil-pbc-category-colimit` supplies the universal property and unique comparison isomorphism. The brief degreewise verification that this is an isomorphism of complexes uses uniqueness against the cocone legs. This ensures the arbitrary supplied colimit cocone is covered, without postulating a derived-category colimit.

For step 2, `def-sfb-dcons-subfield` identifies the full bounded constructible subcategory, and `sk-def-sfb-bounded-constructible` now explicitly uses the locally finitely presented ring-object predicate. This agrees with the constructibility condition written out in `lem-weil-pbc-condensed-sheaf-ext-continuity`. That node supplies all shifted Hom isomorphisms for a constructible sheaf into the same uniformly termwise bounded-below diagram. Its E, Omega, pulled-back coefficient ring, topologically Noetherian X and small index hypotheses match the item, with T=X and M=H^q(K). In particular I have not imported local Noetherianity, a base field for X, a characteristic restriction, or constructibility of the targets. The entire needed comparison is in its statement, rather than inferred from its proof or from its title.

For step 3, `lem-sfb-bounded-cohomology-cone-witness` gives a finite ordered list ending literally in K; each new cone has both earlier indices strictly smaller. I read its source's Complexes paragraph in `sk-cor-coefficient-heart-ii-generation.proof.md`, and Stacks Tag 08J5, label `remark-truncation-distinguished-triangle` in `literature/stacks-project/derived.tex`, including the successive-cohomology triangle. The cone witness is purely about an abelian category and a cohomologically bounded derived object, so it applies to this ordinary module derived category with no geometric extra condition. I wrote the induction explicitly. A triangle F_i -> F_j -> F_r[s] must be rotated before the extension-closure theorem can be used; `def-weil-triangulated-category` states exactly (TR2). The rotated outside terms are F_j and F_i[1], so the induction and shift closure give the two required premises. This avoids incorrectly using an extension lemma as cone closure without explaining the rotation.

Step 4 is elementary unpacking of the fixed comparison predicate. At every stage the transformation is induced by the same cocone legs, so its representative formula is exactly the formula in the item, not an unrelated group isomorphism. The argument uses a finite construction in the first variable and never replaces the target by a presumed categorical colimit in the derived category.

I checked the zero complex, a single sheaf, arbitrary shifts, two adjacent nonzero cohomology groups, and the empty scheme. The zero comparison is between zero groups; a sheaf is exactly the cited base case; shifts reindex the universally quantified integer; two cohomology groups use the displayed rotated triangle once. Unbounded-above targets remain allowed because the sheaf base case only requires the common lower bound. Filtered means nonempty, so an empty indexing category is not an admitted edge case. The proof contains no division by a coefficient or restriction on the characteristic of X. Each non-elementary step is below 2000 characters, and no auxiliary statement is hidden in a long step.

Against B: no new unsplit nodes, implicit settings, unsupported definitions or manufactured leaves occur. Against C: every non-elementary fact is a cited statement, and the quote file contains the actual used clauses. Against D: the proof performs a finite induction using existing strictly smaller ingredients, rather than moving the item into a new name or assuming its conclusion. Against E: all matching hypotheses and objects were checked above; the potentially stronger Noetherian specialization was excluded explicitly. The blueprint is agent-written, so proof_origin.by is agent. No SGA source is used.

## Unfinished work

No mathematical work remains on the requested one-level split. The existing cited nodes retain their own independent proof obligations. Delivery status is recorded below after the required server checks.
