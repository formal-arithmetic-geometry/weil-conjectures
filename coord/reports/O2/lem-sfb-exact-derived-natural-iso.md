# O2: lem-sfb-exact-derived-natural-iso

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-exact-derived-natural-iso.json`: existing statement, now a Mathlib leaf. General localization gives every clause by direct specialization: `CategoryTheory.Localization.liftNatIso`, `liftNatTrans_app`, and `natTrans_ext`, with `CategoryTheory.NatIso.mapHomologicalComplex` as the termwise input. No new nodes. The item itself is one Mathlib leaf.
- `citations.json`: `[]`, because a Mathlib leaf has no proof steps and hence no proof-step node citations.
- `report.md`: this report. `searches.jsonl` was produced by the required search command; its searches and results were read and appended to the item's original search records without deleting those records.

## Attachments

No full attachment is claimed. I searched the project by the blueprint id/docstring tag and by the expected declarations and notion. I read `lean/WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:91-143`. The project declaration `CategoryTheory.Functor.mapDerivedCategoryNatIso` (line 107) constructs the natural isomorphism, and `CategoryTheory.Functor.mapDerivedCategoryNatIso_fac` (line 122) proves the displayed compatibility. Their bodies contain no sorry, but neither statement asserts uniqueness. Thus they do not meet the brief's every-clause ATTACH criterion. The prior `lean_candidates` are retained as partial coverage, not evidence for a full attachment.

## WANTED

None. All sources needed for this item are locally available.

## Findings and changes

The statement is true and unchanged. Its original search verdict classified the localization results as ingredients only. After reading the general statements, I found they cover the entire item under a direct specialization, including arbitrary specified factorization isomorphisms. The Mathlib leaf rule permits one declaration per clause. The `mathlib_match.how` now names each declaration, its file and lines, and the specialization; there is no unresolved comparison of mathematical notions.

I read the chapter record `sec-six-functors-basics` and the unit record `sk-thm-sfb-qlbar-two-colimit`. This item serves the cocone/transitivity sentence of unit step 9, through `def-sfb-derived-extend-comp-iso`. I also read that blueprint node's current `main-20261015` proof: it uses the exact derived functor of the underived scalar-composition isomorphism. The item's existing precise `blueprint.from.place` is retained. Whole-blueprint searches for `natural isomorphism` and `exact functors`, and DAG searches for the tag 04VG and the relevant declarations, found the generic localization universal-property node and specialized derived comparisons, but no blueprint node stating this same generic, normalized, unique induced isomorphism. `same_as` stays empty. No chapter or unit route is replaced, and no unit realization fields need editing because this is not the unit's key node.

## Not duplicates

There are no newly created nodes, so there are no new/existing same-tag pairs. The already existing `lem-weil-pbc-localization-universal-property` is the broader generic Mathlib interface; its statement clauses (2) and (3) directly confirm this classification. The existing `lem-weil-pbc-exact-functor-derived-factorization` supplies the exact functor and its factorization, but does not state natural-isomorphism descent or uniqueness. I read both statements in full rather than extracting facts from their proofs. No duplicate helper is introduced for either fact or for termwise naturality.

## Review by O2

I read delivery-errors B through E, including the repeated new-target versions, with the item, the cited existing statements, and the sources open. Here is the substantive verification of the leaf, clause by clause (there are no numbered proof steps in the delivered leaf).

For the source, I read Stacks `categories.tex`, Tag 04VG, label `lemma-properties-left-localization`, lines 4406-4427. It states functor factorization; it does not itself state the natural-transformation enhancement. I did not attribute that enhancement to Stacks. I read the actual enhancement in Mathlib `CategoryTheory/Localization/Predicate.lean:255-361`: `fullyFaithfulWhiskeringLeft` at 278, `natTrans_ext` at 286, `Lifting` at 295, `liftNatTrans` at 326, its component formula at 332, and `liftNatIso` at 357. I read Stacks `derived.tex`, Tag 015F, label `lemma-right-derived-exact-functor`, and Mathlib `Algebra/Homology/DerivedCategory/ExactFunctor.lean:29-57`, which give the exact functor and its canonical factorization/Lifting instance. No SGA source is used.

The one-line specialization for existence is `Localization.liftNatIso Q_A W _ _ D(F) D(G) (isoWhiskerRight (NatIso.mapHomologicalComplex eta (ComplexShape.up Int)) Q_B)`, where W consists of quasi-isomorphisms. Its source functors are termwise F/G followed by Q_B and its target category is D(B). The assumptions in the item give the derived categories/localization functors and both exact functors. For arbitrary chosen a_F/a_G, instantiate `Localization.Lifting` with exactly these natural isomorphisms; the leaf does not tacitly replace them by some other choice. For the canonical choices, Mathlib already has those instances at ExactFunctor.lean:53-57. No enough-injectives, enough-projectives, small indexing category, or boundedness assumption is introduced.

For the termwise input, I read `Algebra/Homology/Additive.lean:163-207`, especially `NatTrans.mapHomologicalComplex` and `NatIso.mapHomologicalComplex` at 198. Its component in degree n is precisely eta on K^n. Naturality of eta on the differential is the chain-map identity; naturality on each component of a chain map gives naturality in K. The inverse is termwise eta inverse. These are explicit definitions, not a hidden comparison theorem, and additivity supplies the required preservation of zero morphisms. This use is a direct input term to liftNatIso, not a new lemma requiring another DAG node.

For normalization, `liftNatTrans_app` and `liftNatIso_hom` give, in ordinary composition order,

    D(eta)_(Q_A K) = a_G,K^{-1} composed with Q_B(C(eta)_K) composed with a_F,K.

Composing on the left with a_G,K gives exactly the equation in the item, with both sides having source D(F)(Q_A K) and target Q_B(C(G)K). This is cancellation of an isomorphism, not an unproved compatibility. This also checks that the Lean diagrammatic `≫` formula has the correct direction.

For uniqueness, any two candidates satisfying the equation have equal hom components at every Q_A K after cancelling a_G,K. `Localization.natTrans_ext` at Predicate.lean:286 gives equality of their hom natural transformations; `Iso.ext` gives equality of the natural isomorphisms. The item asks for uniqueness among normalized candidates, which is exactly this application; it does not assert there is only one unnormalized isomorphism between D(F) and D(G).

I tested eta = identity (the normalized lift is identity), F = G = the zero functor (the formula still holds), and identity functors with a nonidentity natural automorphism of the identity (the construction retains that automorphism rather than incorrectly forcing identity). I checked arbitrary factorization choices: changing a_F or a_G conjugates the lift by exactly the displayed formula. All formulas are degreewise and make sense for complexes unbounded in both directions, so no bounded resolution is used. There is no disputed statement or source error.

For B, the original statement is self-contained and its three statement dependencies are unchanged; the Mathlib match gives all source lines. For C, there is no unsupported proof-step citation: `proof` and `proof_deps` remain empty as required for a leaf. The existing localization and exact-factorization nodes were read as a cross-check, not falsely cited for stronger statements. For D, nothing is moved into a new restatement; all clauses are direct applications of the general Mathlib declarations. For E, the exactness/localization hypotheses, the source and target of the equation, inverse direction, arbitrary choice of factors, and edge cases were checked above. There are no proof steps longer than 2000 characters to audit.

## Unfinished work

None in the mathematical classification. The required delivery dry run and push are the remaining operational checks when this report is first written; their results are recorded below after completion.

## Delivery validation

The first required dry run completed and refused only the inherited null `proof_origin` field. I repaired that metadata by recording this worker's clause-by-clause specialization at the ancestor blueprint's derived-isomorphism passage; the Mathlib results themselves remain cited in `mathlib_match`. No statement or mathematical match changed. The final dry run is rerun after this repair.
