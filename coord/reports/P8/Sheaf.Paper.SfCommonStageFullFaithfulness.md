## What changed

Proved `WeilConjectures.sfCommonStageFullFaithfulness` in
`Sheaf.Paper.SfCommonStageFullFaithfulness`, preserving its complete statement and all
existing public imports. Four proved private helpers handle injectivity of the
conjugated finite-stage map, its explicit finite-stage preimage, faithfulness of the
pair functor, and fullness of the pair functor. They are generic in the stage systems,
so the proof never unfolds the coefficient categories or their tensor constructions.

The proof reuses `StageSystem.Morphism.tr_mapAt`, `functor_obj`,
`functor_map_mkHom`, and the pair-category representative induction and equality
criterion. Faithfulness follows by transporting two images to a common stage and
using finite-stage injectivity. Fullness follows by lifting a target representative
at its existing stage. Applying faithfulness to the map-preimage equation then proves
the required inverse formula for every representative, including enlarged stages.
The node's proof and proof origin now describe this implementation.

LeanFinder, Loogle, and Mathlib/source-tree searches found the standard
`Functor.FullyFaithful` API and existing stage-system transport API, but no ready-made
full-faithfulness result for a morphism of stage systems. The finished proof uses
that API directly. Edge cases with equal stages and repeated transition witnesses
are covered by the generic calculation and proof irrelevance; no faithful scalar
transition, essential surjectivity, or Karoubi completion is assumed.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.sfCommonStageFullFaithfulness`
(node `lem-sf-common-stage-full-faithfulness`).

The item contains 0 remaining `sorry` declarations. Added 0 holes and split off
0 statements. All four private helpers are completely proved.

Validation: `lcompile.py` compiled the final version without warnings in 5.5 seconds.
The required delivery preflight also checks declaration axioms. Existing dependency
holes are unchanged.

## No longer needed

No imports, dependency nodes, or modules are pruned. The only declared proof dependency,
`def-weil-algebraically-closed-coefficients`, remains needed for the literal pair
category and its representative calculus. Existing public imports support the
published statement and retain their original visibility.

The separate construction and descent of an inverse on quotient representatives is
unnecessary: once fullness and faithfulness are proved, injectivity of the descended
Hom map establishes the inverse formula for every representative. The original
coherence, functoriality, and forward-descent calculations are already proved in
`WeilConjectures.CategoryTheory.StageSystem.Functor` and are reused. No unit-route node
or upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or incompatible dependency was found. The DAG plan repeats
transport and functoriality results that the source-library stage-system API already
proves. Its proof steps were updated to record their reuse and the direct
fullness/faithfulness argument. The unit-normalization hypothesis is retained
verbatim, although the existing conjugation functor does not need it for this result.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
