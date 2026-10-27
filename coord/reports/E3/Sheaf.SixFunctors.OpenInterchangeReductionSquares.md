## What changed

Repair of reviewed head `069cccee765`: K4's `dc9dd96b188` changed the item's public import from `GeneratorReductionStatement` to `GeneratorReductionData` and made the parent import this item through `StructuralReductionWordSubstitution`. That K4 landing was dropped again by `5b5f112c922` (reviewer note: the delivery base `d1fa4910ce8` already contains the drop, so on the current base the item publicly imports `GeneratorReductionStatement`). This delivery keeps the data-only import `GeneratorReductionData` in the extracted data module and the canonical-open lemma, and the combining proof reproduces the existing completion induction as a proved private helper using `PrimitiveCompletionEffectivity` and `ShortWordIntegralDomain`, so no import cycle arises when K4 lands again. No K4 module is edited.

Repair of returned head `325478ad44b`: removed this packet's duplicate creation of `lem-sf-completion-map-is-iso`. T7 has now landed that node with the same Lean declaration and signature. The earlier repair kept its dependency on the existing node; T7's statement, proof metadata, ownership and review records are preserved. No DAG node is withdrawn or deleted.

Replaced the original hole in `openInterchangeReductionSquares` by a complete combining proof. Four named forward generator squares supply beta, open projection, lambda and Gamma. The main module proves the isomorphism and inverse-square clauses and proves whole-system input naturality by induction on words and naturality of the specified maps. It uses a private copy of the published `completionMap_isIso` induction, rather than importing the parent coherence module.

The original eight data declarations are moved verbatim to `OpenInterchangeReductionData` and publicly re-exported by the original module. All original public imports remain publicly available through that data module. The main theorem signature is unchanged. No source-library module or module held by another group is edited. The change record is `coord/changes/E3-open-interchange-reduction-data.md`.

## Proved and sorry left

Validation of the rebased source: six support modules compiled in the server batch; the final main file compiled cleanly in 58.4 seconds. Profiling identified broad simplifications; the final proof uses explicit definition lists and identity rewrites, with all profiler options removed.

The original item had one hole: `WeilConjectures.OpenInterchangeReduction.openInterchangeReductionSquares`. Its new combining proof has zero holes. Four holes are added in separate modules (reviewer correction: the fifth new statement, `canonicalOpenReduction_isIso`, is proved by the library's `fixedOpenReduction_isIso` of `OpenReconstructionEffectivity`, imported with `import all`):

- `WeilConjectures.OpenInterchangeReduction.openBaseChangeReductionSquare` (`lem-sf-open-base-change-reduction-square`).
- `WeilConjectures.OpenInterchangeReduction.openTensorReductionSquare` (`lem-sf-open-tensor-reduction-square`).
- `WeilConjectures.OpenInterchangeReduction.properOpenLambdaReductionSquare` (`lem-sf-proper-open-lambda-reduction-square`).
- `WeilConjectures.OpenInterchangeReduction.properOpenInterchangeReductionSquare` (`lem-sf-proper-open-interchange-reduction-square`).

`WeilConjectures.GeneratorReduction.canonicalOpenReduction_isIso` (`lem-sf-canonical-open-reduction-is-iso`) has no hole of its own: it is `fixedOpenReduction_isIso l E o.system o.realization j K`, which rests on the existing statements `ordinaryOpenReduction_isIso` (lem-sf-ordinary-open-reduction-mate) and `openReduction_mate_localization` (lem-sf-open-reduction-mate-localization).

Each forward-square lemma is just one of the four constructor cases, without the other cases, inverses, isomorphism or input naturality clauses. The ambient invertibility lemma supplies naturality of the inverse canonical open comparison used in the induction; it does not assert any generator square. The private `completionMap_isIso` helper copies the existing proved induction with the same hypotheses and conclusion; it adds no hole. No definition or private helper contains a hole.

The edge cases include empty and identity opens and zero inputs; the recorded representative formulas remain the same in these cases. The noncartesian proper/open case has no hidden pullback assumption. The internal clopen factorization uses all six systems in generator admissibility, including length-four intermediates; the length-three bound is only on the generator endpoints.

## No longer needed

Removed direct proof imports `Sheaf.Paper.SfImmersionCompletedPullbackComparison`, `Sheaf.SixFunctors.OpenFactorTensorModel`, `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`, `Mathlib.CategoryTheory.Adjunction.Mates`, and `Mathlib.CategoryTheory.Adjunction.Basic` from the main module. Their needed mathematical content is recorded under the forward-square lemmas; they are not claimed globally pruned. Every original public import is retained in the extracted data module.

The final packet uses no new general context-closure, ringed-word cancellation or ambient beta/tensor interface modules. Those exploratory splits were not delivered. The main naturality proof proceeds directly by induction. The parent module `GeneratorReductionStatement` and its completion-map node are no longer direct dependencies of this item; the published declaration remains needed elsewhere and is unchanged. No existing module is withdrawn: the four forward cases retain the original unit route and planned dependencies.

## Where the brief, the DAG or earlier work was wrong

The item's data predicates had to be extracted before the forward cases could use them without importing the theorem module. Their definitions and the original public import environment are preserved verbatim.

K4's parent coherence proof (which imports this item via `StructuralReductionWordSubstitution` and changed the item to import `GeneratorReductionData`) was landed in `dc9dd96b188` and dropped again in `5b5f112c922`; this delivery keeps the data-only import so that it stays compatible when K4 lands again. The private completion induction depends directly on `lem-sf-primitive-completion-effectivity` and `lem-sf-short-word-integral-domain`, so no proof dependency or Lean import returns to the parent. The existing completion-map node is untouched and is no longer a direct dependency of this proof.

The dispatcher reset `.budget` for the repair of `069cccee765` (previous repair head `325478ad44b`). No worker change to clock metadata was made.

The public `openReconstructionEffectivity` has a completeness hypothesis, but its private first half `fixedOpenReduction_isIso` holds for every input and closes the ambient open-mate invertibility lemma (reviewer correction). Attempts to close all four cases encountered substantial category-alias and completion-map normalization glue; the final packet retains the larger, source-based generator calculations and the completed inverse/naturality assembly.

## New nodes

`def-sf-open-interchange-reduction-data` attaches the eight unchanged definitions.

`lem-sf-open-base-change-reduction-square` records the forward beta calculation.

`lem-sf-open-tensor-reduction-square` records the forward open tensor calculation.

`lem-sf-proper-open-lambda-reduction-square` records the forward four-factor lambda calculation.

`lem-sf-proper-open-interchange-reduction-square` records the forward Gamma calculation.

`lem-sf-canonical-open-reduction-is-iso` records ambient open comparison invertibility.

The calculation nodes retain the relevant original proof steps and sources. `lem-sf-completion-map-is-iso` already exists on the current main branch and is not delivered or modified. The private induction uses its two lower dependencies directly. The change record is `coord/changes/E3-open-interchange-reduction-data.md`.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
