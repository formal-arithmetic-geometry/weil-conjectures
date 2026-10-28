## What changed

Filled the identity transport and successive-composition Hom coherence proofs in
`Sheaf.Paper.PodReindexingCompletedEvaluationReflection`. Their public statements are unchanged.
The coefficient-isomorphism uniqueness argument is reused in a proved private helper;
the existing proof of `reindex_eq` stays verbatim. Private categorical lemmas compare section-normalized ordinary isomorphisms, identify
their derived images from the recorded degree/model equations by localization extensionality,
and transport the existing ambient Hom coherence laws through the reindexing equalities.
Concrete specializations keep the isomorphisms abstract during these categorical calculations,
so kernel checking does not unfold the derived identity and compositor constructions.

Added two proved generic normalization modules,
`Sheaf.Paper.PodReindexingDerivedIdentityNormalization` and
`Sheaf.Paper.PodReindexingDerivedCompositionNormalization`, imported only for proofs.
They use the existing derived natural-isomorphism functoriality and whiskering API through a
private import of `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
Updated the four attached DAG proof records to describe the actual argument. Existing public definitions and statements are unchanged. The exactness witnesses come from
the existing sectionwise inverse-image theorem. Their instance registrations and the extra
reducibility attributes are local to the coherence proof section.

## Proved and sorry left

Closed 2 of the original 2 holes:

- `WeilConjectures.PodCompletedReflection.identity_transport_data`
  (`lem-pod-reindexing-completed-evaluation-reflection-identity-transport`).
- `WeilConjectures.PodCompletedReflection.identity_composition_composition`
  (`lem-pod-reindexing-completed-evaluation-reflection-composition`).

Holes added: 0. Holes left in the item: 0. No unproved statements split off.
The two new public theorems
`WeilConjectures.podReindexingDerivedIdentityNormalization` and
`WeilConjectures.podReindexingDerivedCompositionNormalization` are proved.
All added private helpers are proved; the existing ambient coherence declarations supply the
remaining mathematical dependencies as intended by stage 3.

Validation: both new normalization modules compile independently. The complete reflection
module compiles in 48.9 seconds, below the 60-second limit. All 27 original public signatures
are unchanged and contain no private constants from the item. All three delivered Lean modules
contain zero `sorry` occurrences.

## No longer needed

No existing module is withdrawn and no original import is removed. The new derived-functor
API import is confined to the normalization modules; the reflection module imports their
proved normalization theorems instead. The identity and composition conjunct nodes
no longer need the proof-dependency edges to
`lem-pod-reindexing-completion-unit-tensor` and
`lem-pod-reindexing-tensor-augmentation-square`: their proofs use ordinary section normalization,
localization, and the ambient Hom coherence equations. Those nodes and their modules remain
needed elsewhere in this item's completed-tensor and reindexing proofs. Also removed the
identity/composition conjunct citations from the main node's currying and evaluation steps,
which do not use them; those conjuncts remain required in its coherence step. The unit route stays.

## Where the brief, the DAG or earlier work was wrong

The two conjunct nodes still described stating the conjuncts rather than proving them, and the
main node still referred to a remaining identity/composition hole. The updated records give the
sectionwise comparison, uniqueness of the derived normalization, and the actual categorical
transport calculation. No mathematical statement was repaired or weakened.

## New nodes

`lem-pod-reindexing-derived-identity-normalization`, in
`dag/nodes/sec-poincare-duality/lem-pod-reindexing-derived-identity-normalization.json`,
records the fully proved generic identity normalization theorem in
`Sheaf.Paper.PodReindexingDerivedIdentityNormalization`. Its model equation determines the
normalized derived isomorphism by localization; exact-functor functoriality transports the
ordinary equality to the derived identity equality. It has no new mathematical hypothesis
on the reflection theorem and introduces no hole.

`lem-pod-reindexing-derived-composition-normalization`, in
`dag/nodes/sec-poincare-duality/lem-pod-reindexing-derived-composition-normalization.json`,
records the fully proved generic compositor normalization theorem in
`Sheaf.Paper.PodReindexingDerivedCompositionNormalization`. Cancel the two complex factors
and use localization to determine the derived compositor, then apply derived natural-iso
functoriality and both whiskering formulas. It introduces no hole. These two lemmas are
strict parts of the sectionwise-to-derived transport argument, and preserve the unit route.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingCompletedEvaluationReflection": "2cd791a91f709fb971ab213014290bdd16b26db4", "Sheaf.Paper.PodReindexingDerivedCompositionNormalization": "a85d271ed1cb4572fa31e9d87133fd38980dc0d6", "Sheaf.Paper.PodReindexingDerivedIdentityNormalization": "d571d46a9f7ba108c1d2d76f833c81a7d8fd1b36"}, "results": {"Sheaf.Paper.PodReindexingHomCoefficientDescent": {"hash": "9689050e964af829992911358e320fa4ee5c5ac1", "status": "SLOW"}}, "seconds": 131, "time": "2026-10-28T10:35:40+0800", "transitive": 0, "version": 1}
```

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
