# Stage-1 delivery: lem-sfb-flat-geometrically-reduced-pullback

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-geometrically-reduced-pullback.json`: existing statement item, confirmed Mathlib leaf.
- `report.md`: this report and signed review.
- `citations.json`: empty list, because a Mathlib leaf has no proof steps or proof citations.
- `searches.jsonl`: unmodified output log of the required search command.

No new nodes. One Mathlib leaf is completed (the item).

## Attachments

None. I searched the live `lean/WeilConjectures/` by the exact blueprint tag and by `GeometricallyReduced`, geometrically reduced, flat reducedness and pullback instance names. The project extension files contain smooth/perfect-field reducedness and composition results, not this exact statement. The exact declaration is in Mathlib, so this is a leaf delivery rather than an ATTACH claim.

## WANTED

None for this item. Its primary source is the locally available pinned Mathlib source. The inherited provenance mentioning a wanted Vidal article concerns the parent alteration argument; no Vidal assertion is used here.

## Findings and corrections

The seeded candidate is correct: `AlgebraicGeometry.instIsReducedPullbackSchemeOfGeometricallyReducedOfFlatOfIsLocallyNoetherian_1`, `Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean`, lines 128–130. Set X=T, f=(T → S), Y=Y, g=h. The four typeclass hypotheses are exactly the given geometric reducedness, flatness, reducedness of T, and local Noetherianity of T. The conclusion is reducedness of the ordinary pullback in the stated order T ×_S Y. No finite-type, finite-presentation, separation or Noetherianity hypothesis on S or Y is added.

The item had doubled literal TeX backslashes. I normalized them to single backslashes in the decoded statement, without changing its mathematical content. No mathematical statement dispute was found. Historical searches are retained verbatim, and the new actual searches are appended with individual verdicts. The historical finite-extension wording in a search is not an additional hypothesis or a lemma used by this item.

`tools/blueprint_refs.py ancestor` returns None: this chain ends at a module-created input rather than an imported blueprint node. I retain the inherited null ancestor and detailed place/via chain. Searches of the whole imported blueprint for “geometrically reduced”, “reduced pullback”, and “flat geometrically” found no imported statement of this lemma; `same_as` remains empty. This item is a supporting lemma, not the key statement of its unit; no unit realization file is changed.

## Not duplicates

No new node is introduced. The already existing item `lem-sfb-flat-geometrically-reduced-pullback` vs `lem-per-flat-geometrically-reduced-pullback`: the statements are identical (up to the same TeX rendering issue), and both refer to the same Mathlib instance. The latter is already a Mathlib leaf under a different alteration branch. This was a pre-existing duplication, not a new lemma of this delivery. The maintainer should consolidate these nodes and repoint users under the normal merge protocol; I have not changed the other node or any user's dependencies. The present delivery only confirms the assigned existing item's exact Mathlib match.

## Review by NJ

I read delivery-errors B–E in both copies of that file and checked the actual pinned source rather than relying on the seeded verdict. For the item I read Reduced.lean lines 39–60 and 73–130, especially the source proof at 109–118 and the second-factor pullback instance at 128–130. I also read Geometrically/Basic.lean lines 44–49 and 88–100: the universal field-valued pullback condition is exactly the geometrically reduced class. Basic.lean's isomorphism-invariant characterization identifies the chosen fibre product with the arbitrary pullback formulation; this is already supplied by Mathlib, not a new geometric comparison theorem.

I opened the statements of every statement dependency: def-pc-scheme defines schemes and their morphisms; def-weil-flat-morphism defines stalkwise flatness; def-weil-field supplies fields; def-weil-affine-spectrum supplies Spec K and its scheme structure; def-pc-fibre-product supplies the ordinary scheme pullback; def-pc-reduced-scheme supplies reducedness; pqf-def-locnoeth supplies local Noetherianity. Each defines the notion it is cited for. There are no proof steps and therefore no C4 proof citations to quote or C1 hidden inputs to create. `proof` and `proof_deps` stay empty, and `citations.json` is empty. No long proof step exists.

I compared the hypotheses and both factors directly: the flat geometrically reduced map is the second map g=h; only the first source X=T must be reduced and locally Noetherian. The source theorem does not require T → S to be flat, nor Y to be reduced independently, nor either map to be locally of finite presentation. This avoids replacing an ordinary fibre product with its reduction or applying a theorem with extra finiteness assumptions.

Small cases checked mathematically: T empty or Y empty gives the empty reduced scheme; h=id_S gives the reduced scheme T; S=Spec K and Y a geometrically reduced scheme gives the expected scalar-base pullback. In characteristic p a nontrivial purely inseparable field extension L/K is a useful boundary test: Spec L → Spec K is flat, but L ⊗_K L has nilpotents, so it fails the field-valued reducedness hypothesis and is correctly excluded. No claim is being made for nonreduced T. These checks agree with the exact source statement.

I inspected the only same-statement DAG hit, lem-per-flat-geometrically-reduced-pullback, and reported it above rather than creating a further duplicate. The Mathlib leaf adds no proof edge, no circular dependence, and no alternate unit route. No Lean file or repository/launcher file was written, no compiler or Lake command was run, and all authored files are in this item's sandbox.

## Unfinished work

No mathematical work remains for this item: its exact Mathlib declaration is identified. Consolidating the pre-existing duplicate is maintainer work outside this item's delivery scope. Required dry run and delivery results are reported by the delivery command.
