# Stage-1 report: lem-sfb-relative-flat-fibre-test

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-flat-fibre-test.json: statement, now split; no Mathlib match for the full statement.
- citations.json: one exact statement excerpt for every node used by every proof step.
- report.md: this report.
- searches.jsonl: search command's own records, retained without editing.

No new nodes and no new Mathlib leaves. The three permanence results used are existing Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, relative flat-fibre names, flatness/fibre keywords, and pointwise flatness equivalence names. The closest general fibre result found in WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean is a smoothness criterion assuming flatness, not this assertion. The existing dependency's Sheaf/AlgebraicGeometry/FibrewiseFlatnessCriterion.lean declaration Scheme.Hom.flatAt_and_base_flatAt_of_fiber_flatAt ends in sorry and states only the reverse implication; it cannot attach this item. Source declarations are not evidence of finished proofs here.

## WANTED

None. All source passages needed were available in literature/stacks-project/.

## Findings and changes

The imported statement is correct and remains byte-for-byte unchanged, as do its statement dependencies. Its proof was empty. The proof now explicitly identifies the cartesian fibre square, uses pointwise base-change ascent for the forward implication, uses the existing structure-sheaf fibrewise-flatness criterion for the reverse implication, preserves all three hypotheses under arbitrary parameter change, and repeats the established argument over the new parameter scheme. There is no assumption that the fibre inclusion or parameter change is flat.

I read the chapter and unit records, the current latest blueprint unit and its direct-images proof (3), and the item's inherited source/ancestry. The existing unit record comes from an older blueprint route, whereas the latest direct-images proof uses compactification and the stated direct-image inputs. This small scheme-theoretic prerequisite does not modify either route or a unit realization field. The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor lem-sfb-relative-flat-fibre-test reports None for the existing created.item chain. I preserved that metadata and its long explicit place/via chain rather than invent an ancestor or edit another node. The blueprint searches 'criterion-flatness-fibre', 'fibrewise flatness', and 'flatness fibre' found no matching imported node. 'flat base change' found eight nodes on other subjects, none stating this test.

No statement dispute, source error, or unfinished mathematical argument was found. No Lean file was written and no compiler, Lake, or build tool was run. All writes are in the assigned sandbox.

## Mathlib searches

The item already contains its creator's earlier search records; those are retained. I added only the actual results of this attempt's msearch.py calls: LeanFinder with two different phrasings, Loogle with Flat/LocallyOfFinitePresentation/fiber, LeanSearch in words, and grep of AlgebraicGeometry for flatness/fibre criteria. I read the returned declarations and Mathlib/AlgebraicGeometry/Morphisms/Flat.lean and SmoothFiber.lean. The hits supply definitions, global stalk tests, localization, and preservation of a flat map, or smoothness after assuming flatness; none supplies this relative pointwise equivalence. Every service responded successfully. No unavailable service is misreported as a negative search.

## Not duplicates

No new nodes were created. In particular, I reused lem-sfb-fibrewise-flatness-criterion (039C) and lem-sfb-pointwise-flatness-base-change (047C), instead of introducing nodes for those already stated facts. I searched the whole DAG for both tags and read the relevant statements. For finite-presentation permanence I reused clause (3) of lem-weil-pbc-qcqs-morphism-permanence, which already covers arbitrary scheme morphisms without a qcqs hypothesis in that clause. Its title alone would not have been sufficient evidence; its actual statement is.

## Review by Q48

I read More on Morphisms Tag 039C (theorem-criterion-flatness-fibre), Tag 05VJ (lemma-base-change-criterion-flatness-fibre), and Tag 047C (lemma-flat-locus-base-change). I also read Schemes Tags 01K0 and 01K1 and Morphisms Tags 01U9, 01TS and 01T4 in the local TeX source. There are no new nodes needing additional source validation.

Step 1 uses the actual statements of def-pc-fibre-product and def-pc-scheme-fibre. The first gives existence, uniqueness and the universal property; the second gives the homeomorphism onto the set-theoretic fibre. The argument describes maps from a test scheme to both candidate pullbacks, so the identification X_s = X times_Y Y_s is proved rather than assumed. The projection identities and unique fibre points give f_s(x-tilde) = y-tilde. This is a routine universal-property argument, marked elementary, not an unproved comparison lemma.

Step 2 cites exactly clause (1) of lem-sfb-pointwise-flatness-base-change. Its statement permits an arbitrary target base change and needs only flatness at the projected point. The square established in step 1 and its point x-tilde meet those hypotheses. No use of clause (2), and thus no flatness hypothesis on i_Y, occurs.

Step 3 cites def-weil-flat-morphism to extract pointwise flatness of p from global flatness. The statement of lem-sfb-fibrewise-flatness-criterion requires precisely local finite presentation of p, local finite type of q, and pointwise flatness of p and f_s. These are all hypotheses of this item or the assumption of this implication. The lemma's conclusion includes f flat at x as well as q flat at y. Retaining the former is legitimate; q flat is not silently assumed. In the structure-sheaf reading of 039C the stalk is nonzero at a scheme point, so the theorem's nonzero-stalk condition causes no exceptional case.

Step 4 reads and cites the full statements of lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence clause (3), and lem-weil-pbc-lft-base-change. They respectively give flatness, local finite presentation, and local finite type after any scheme base change. In particular the qcqs conditions in clauses (1) and (2) of the middle node are not premises of its independent clause (3). These nodes are existing Mathlib leaves, so their use is not an off-unit route replacement. The two non-Mathlib proof tools in steps 2 and 3 belong to this item's own unit.

Step 5 uses the previously proved implications with explicit substitutions. The equation q_T f_T = p_T follows from the defining projection equations, and step 4 supplies all hypotheses. This final logical instantiation is elementary; it does not cite a new node restating the item and does not assume the desired base-changed result.

I checked delivery-errors B through E point by point: no new-node form or hidden proof obligations, every used notion already defined by a statement dependency, genuine TeX escapes, exact tag labels, no duplicate or re-labelled clause, and each non-elementary fact covered by an actual cited statement. citations.json contains literal substrings of those statements, checked before writing. proof_deps is exactly the union of step uses. The proof uses no descendant of this item; the reverse criterion and ascent lemma have independently split dependencies. All steps are shorter than 2000 characters (588, 282, 456, 483, 355), so there is no long step hiding a lemma.

For small cases I checked an empty source or empty T (the pointwise claims are vacuous and all permanence assertions hold), identity parameter change (the original argument is recovered), a field base (the criterion is consistent with the original fibre map), and a nonflat closed-point parameter change Spec k -> Spec k[t]. The last case is covered because base-change preservation of p, and not any flatness of h, is what the proof uses. No affine-intersection, separation, global finiteness, or Noetherian assumption is introduced.

## Unfinished work

None within this stage-1 item. Its cited existing nodes retain their independent status and are not edited by this delivery.
