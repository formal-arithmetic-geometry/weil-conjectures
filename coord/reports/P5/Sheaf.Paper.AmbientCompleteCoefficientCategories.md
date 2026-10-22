## What changed

Filled all eleven construction and coherence proofs in
`Sheaf.Paper.AmbientCompleteCoefficientCategories`. The integral inclusion commutes
with the tensor functors and their specified associators. Localization gives the
strict raw inclusion squares and their coherent comparisons; Mathlib's Karoubi
extension preserves their units and tower equations. The common-stage inclusion
and identity-projector embedding then descend by the existing pair-functor API.
The representative formulas prove additivity.

Finite biproducts follow from the additive completion functor: its unit-isomorphism
locus is closed under finite coproducts. Localization and Karoubi completion
preserve the resulting sums. Adapted only the associator equality proof in the unclaimed consumer
`Sheaf.Paper.FiniteStageKaroubiExtension`; its signatures and attributes stay unchanged.
Private proved helpers isolate these generic
arguments from the concrete derived categories. The node's proof record now
follows the Lean argument.

Normalized the existing aliases and canonical comparison definitions, supplied
explicit functor result types, and made the finite-stage inclusion irreducible.
Both complete systems retain their original inline constructors and data.
A private generic stage-system lemma handles the raw inclusion tower once,
including repeated coefficient fields, before specialization.
Two generic typed Karoubi constructors check the functor-composition conversions
abstractly, avoiding repeated expansion of concrete tensor functors.
The formulas retain both projectors and have the same mathematical meaning;
see `coord/changes/P5-ambient-complete-stage-alias.md`. Proof imports use the public
uniform-complete triangulation theorem rather than its duplicate private helper.

## Proved and sorry left

The eleven original holes have complete proofs:

- `AlgebraicGeometry.Scheme.pbcCompleteKaroubi_cocycle`
- `AlgebraicGeometry.Scheme.pbcCompleteSystem_units`
- `AlgebraicGeometry.Scheme.pbcCompleteRawInclusionComparison_exists`
- `AlgebraicGeometry.Scheme.pbcCompleteInclusionComparison_exists`
- `AlgebraicGeometry.Scheme.pbcCompleteInclusion_coherent`
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteTransition_additive`
- `AlgebraicGeometry.Scheme.pbcConstructibleCompleteTransition_additive`
- `AlgebraicGeometry.Scheme.pbcCompleteStages_finiteBiproducts`
- `AlgebraicGeometry.Scheme.pbcCompletePairInclusion_additive`
- `AlgebraicGeometry.Scheme.pbcRawStageToCompleteComparison_exists`
- `AlgebraicGeometry.Scheme.pbcRawPairToComplete_coherent`

No holes added or split off; no `sorry` remains in the item source.
Validation: `lcompile.py --all` passed for the actual item and all eight current
transitive consumers. The item took 52.8 seconds; the adapted consumer took 6.9
seconds, and every other consumer also passed within the per-file limit. The checked
consumers were `FiniteStageRationalExchangeData`, `QbarCoefficientSmoothBaseChange`,
`FiniteStageKaroubiExtension`, `RationalRawOperationCoherence`,
`RationalRawSquareExchangeCoherence`, `RationalOperationCoherence`,
`RationalSquareExchangeCoherence` and `FiniteStageRationalExchangeCoherence`, all
under `Sheaf.Paper`. The seven unchanged consumer copies were then removed from
the packet. Original theorem headers are unchanged. The compiled original confirms
that the finite-biproduct theorem already has its current three geometric assumptions.

## No longer needed

The proof no longer uses `CategoryTheory.Idempotents.coefficientCompositionIso`;
its public declaration remains available. Its identity adapters are omitted from
the three extended comparisons. No modules or DAG nodes withdrawn. No imports removed. The statement dependencies
remain necessary for the two finite-stage and two outer Karoubi layers.

## Where the brief, the DAG or earlier work was wrong

The definition node had no proof steps even though its Lean realization contained eleven
construction and coherence theorems with holes. The updated proof record describes those
arguments. No target statement or mathematical definition was weakened.

## Forced adaptations

`Sheaf.Paper.FiniteStageKaroubiExtension` is unclaimed. Its unchanged original failed
against the changed item at line 58, `exact composition_adapter _ _ _ _`, with:

```text
typeclass instance problem is stuck
  Category.{?u.121, ?u.120} ?m.141
```

The typed associator constructor hides the `mapIso` expression from that adapter's
argument inference. The two replacement proof lines unfold
`coefficientAssociatorIso` and use `rfl`: both sides are then the identical supported
Karoubi `mapIso`. Every existing signature, visibility and attribute is unchanged,
and the private adapter remains in the file. The unchanged original failed before adaptation; the adapted file passed in the
full consumer check above.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
