## What changed

Proved `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerModulePull_exact`
using Mathlib's pointwise preservation instances for whiskering right. The finite-limit
and finite-colimit structures are built from their instances for each finite shape.
The only added Mathlib import is proof-only:
`Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`.

Reduced `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerComplete_iff_intrinsic`
to the unit-compatible Koszul-to-quotient comparison in the actual completed coefficient
presentation. For any generators and representative the proof cancels the comparison
isomorphism using `isIso_comp_right_iff`. In the converse, finite generation supplies
one generating family and the localization supplies a representative. All original
signatures, definitions, public imports and instance declarations are unchanged.

The complete packet compiled and passed the delivery preflight in the dry run.
The only remaining hole is the named comparison described below.

The comparison is isolated in the new proof dependency
`Sheaf.Paper.CompletedKoszulQuotientComparison`. The completed-pullback node records
the categorical argument; its existing Qbar declaration attachment is unchanged.

## Proved and sorry left

The original module had two holes and now has zero textual holes.

- Proved: `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerModulePull_exact`.
- Decomposed: `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerComplete_iff_intrinsic`.
  Its categorical proof is complete, conditional on the comparison below.
- Added and left with `sorry`:
  `AlgebraicGeometry.Scheme.completedKoszulQuotientComparison`, node
  `lem-weil-pbc-completed-koszul-quotient-comparison`.

Thus this delivery proves one original hole and decomposes one into one separate
reconstruction comparison; it does not claim two completed mathematical proofs. The new
lemma is the object-and-unit comparison step of the source argument, for a fixed
list and representative. It neither states the completeness equivalence nor quantifies
over all generating lists and representatives as that equivalence does. The main proof
supplies the invertibility argument and the nonvacuity argument from finite generation.
The comparison includes empty lists, zero rings and empty schemes, with no completeness
assumption on the input. Its source and full proof in words are in its docstring and node.

## No longer needed

No original public import, unit statement or unit proof step is removed. No module is
claimed pruned from the target closure. The exactness proof needs no additional Sheaf
lemma. The new comparison is a proof-only import in CompletedPullback.

The abandoned sandbox attempt to compare the two derived constant-limit units directly
used `Sheaf.Paper.CompletedTowerDirectImage`; that additional import and its private
helper are absent from this packet. They were not part of the repository baseline, so
this is cleanup of the attempt rather than a claim of library pruning.

`Sheaf.Paper.KoszulReconstruction` and
`Sheaf.Paper.ConstantCompletionEquivalence` are not imported directly by the consumer:
their mathematical comparison is the source of the separate presentation-specific
comparison node. Their incompatible interfaces are not silently identified.

## Where the brief, the DAG or earlier work was wrong

The completed-pullback definition node attaches to
`Sheaf.Paper.PbcQbarCompletedPullback`, not this module; its original proof fields were
empty. This packet records the supplementary proof of the strict completed-coefficient
interface without changing that attachment or the definition statement.

`koszulReconstruction` uses `A : Type t` for `T : Scheme.{t}`,
`CompletedAdicModules`, and `reconstructionCompletionUnit`. This item instead uses
`A : Type (t + 1)`, `reductionModules`, and the derived constant/limit adjunction unit.
The generic constant-completion theorem uses a small ringed-site presentation with
another normalized reduction tower and unit. These differences require actual
presentation and unit-normalization comparisons, not a direct application or `rfl`.

A further route through the recently landed
`WeilCompletedKoszulLimitComparison` was attempted. Its prerequisite
`WeilCompletedKoszulRoosComparison` was not available in the server's compiled baseline;
that failed attempt is retained only in scratchpad, with no unavailable import delivered.
The current blueprint reconstruction source is in sec-proetale-coefficients,
order 1316; the older module docstrings use order 1248. The node source path has
been corrected to the current snapshot.
The earlier report claiming no added hole was stale and has been replaced by the explicit
hole accounting above. No arbitrary object is chosen from the new theorem in a definition.

## New nodes

`lem-weil-pbc-completed-koszul-quotient-comparison`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-completed-koszul-quotient-comparison.json`,
records the separately sourced comparison of the explicit Koszul fiber and actual
strict quotient limit, carrying their specified units to each other. It is the
reconstruction assertion used in the last paragraph of completed pullback, specialized
to the coefficient universe and normalization of this module. There are no definition
changes and no change records.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
