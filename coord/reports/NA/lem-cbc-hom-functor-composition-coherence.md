## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-hom-functor-composition-coherence.json`: the existing item, split into six proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: 17 verbatim quotations covering every cited node in every proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the exact item id, coherent Hom/functor composition terminology, twisted-arrow terminology, and likely declaration names. No project declaration states the item exactly. No declaration with this blueprint tag was found, and no sorry-free attachment exists.

## WANTED:

- An archived copy of Kerodon 046J, 03PD, 03N3 and the twisted-arrow classification material 03N6/03N7; the repository source is an online Kerodon reference and says no Stacks tag states this quasicategorical result.

## What was wrong or changed

The imported item was unsplit and had an empty proof. Its statement is retained verbatim. The split follows the imported auxiliary role: it makes the twisted-arrow classification and strict composition normalization explicit, then derives the postcomposition homotopies used by `lem-cbc-coherent-square-comparison-data`. No statement clause was weakened, no coefficient category was changed, and no new node was introduced. The existing blueprint search found no second blueprint node stating this result. No source error or statement dispute arose.

## Not duplicates

No new nodes were created. The existing `lem-coef-infinity-hom-bifunctor-functoriality` is cited rather than duplicated: it gives Hom actions and coherent single-functor naturality, while this item adds the strict twisted-arrow classifier and composition comparison for two composable functors. The existing `lem-coef-twisted-arrow-left-fibration` gives the classifier construction and left-fibration property, while this item applies its functoriality to normalized Hom transformations. The existing `lem-coef-space-transport-classification` gives the classification equivalence and compatibility of comparisons, while this item specializes it to the Hom classifiers and the displayed postcomposition path.

## Review by NA

I read the item node, the `sk-prop-sf-cbc` unit, the `sec-smooth-purity` chapter, the ancestor blueprint file `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/thm-cbc-finite-level-proetale.md`, and the current statements of all four proof dependencies. The item’s `blueprint.from` already points to the finite-level pro-etale ancestor and its auxiliary Hom-functor composition compatibility; `same_as` remains empty after a whole-blueprint search.

Step 1 uses `lem-coef-twisted-arrow-left-fibration` for the explicit definition of `Tw(C)` and the assertion that its map to `C^op × C` is a left fibration, and `lem-coef-space-transport-classification` for classifying that left fibration as a space-valued Hom functor. The quoted `def-cbc-enhanced-diagrams-cones` sentence supplies the meaning of coherent diagrams, transformations, and higher simplices. I verified that the step introduces only small quasicategories and uses the node’s stated Kan-space/mapping-space framework.

Step 2 uses the twisted-arrow node’s statement that its constructions commute with simplicial functors, the transport node’s explicit mapping-space equivalence over a fixed base, and the Hom-functor node’s statement that a coherent functor induces the mapping-space transformation obtained by applying it to every right-pinched simplex. These statements justify both the actual fiber map `T_{x,y}` and its coherent transformation data; no property is taken from a cited proof.

Step 3 uses the transport node’s verbatim assertion that its comparison is coherent in both functors and compatible with composition and pullback. The strict degreewise equalities `Tw(1_C)=1` and `Tw(UT)=Tw(U)Tw(T)` are written out, so the constant comparison for equal composites is an elementary consequence of the displayed definitions. The enhanced-diagram definition supplies the higher simplices retained in the strict diagram.

Step 4 uses the Hom-functor statement that the second-variable action is postcomposition and that induced maps preserve canonical composition and identity classes. Restricting the stated coherent naturality to the identity point and an edge gives exactly the normalized homotopy `h_T`; the transport compatibility explains why this is the classified normalization rather than an arbitrary independently prescribed homotopy.

Step 5 applies the same transport composition compatibility to the two functors `T` and `U`. I checked the object and edge hypotheses in the displayed path: both composites act on a right-pinched simplex by the identical simplicial map because functor composition is strict. The relative-endpoint conclusion is the 2-simplex supplied by the Kan mapping space in the transport statement, with endpoints the normalized `h_{UT}` and the pasted `Uh_T`/`h_U T` path.

Step 6 restricts the preceding constructions simultaneously to the finite strict ordinary diagram. The enhanced-diagram definition supplies coherent higher simplices, while the transport and Hom nodes supply composition/pullback coherence and preservation of composition. Equal composites are equal before classification, so no additional choice is needed. I checked that this step assembles the item’s simultaneous-normalization clause rather than restating a separate lemma.

I checked every entry of `citations.json` against the verbatim statement text of its node, and `proof_deps` is exactly the union of the step uses. Every step is below 2000 characters. I tested the construction on identity functors, composable identities, a discrete quasicategory, the terminal quasicategory, and empty mapping spaces: the twisted-arrow maps are then literal identities or empty-fiber maps and the displayed homotopies are constant. The Mathlib searches were rerun through `msearch.py` in both semantic and syntactic forms; returned declarations concern ordinary simplicial composition or truncated homotopy categories, so the item has no Mathlib match. No Lean file was written and no compiler, Lake, or build command was run.

## Unfinished work

No part of this one-level split remains unfinished. The item’s cited Kerodon references remain wanted as archival literature, and the cited generic nodes retain their own stage-1 states.
