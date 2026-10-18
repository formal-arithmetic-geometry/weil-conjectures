## What changed

Proved `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence`
in `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`, preserving its exact
statement and preserving `proEtaleOpenExtensionComp` unchanged.

The proof uses the existing canonical comparison isomorphism. It identifies the
etale and pro-etale extension-composition maps as conjugates of literal restriction
composition. The etale pullback/restriction calculation reuses the proved
`Etale.upperStarComp_hom_comp_upperStarIsoLocalizationRestriction` in HeartGluing;
the pro-etale calculation is proved on sections. The proved general theorem
`CategoryTheory.adjunctionSquareComposition` then supplies composition coherence.
The identity law follows from the same conjugation calculation with identity
restriction. Invertibility is inferred from the existing natural isomorphism.

All added helpers are private and fully proved. No intermediate module, new
statement obligation, arbitrary choice, or change of an existing definition is used.
A generic cancellation lemma prevents the final simplification from unfolding
large extension-by-zero constructions. The node's proof and proof dependencies
now describe this route.

The import-interface change is documented in
`coord/changes/Q4-extension-zero-comparison-proof-imports.md`. The source scan
`tools/downstream.py` found zero downstream modules, so no consumer adaptation
is required. The public declarations retain their original signatures and visibility.

Validation: the final module compiles without warnings through `lcompile.py`
(40.4 seconds). The delivery parser reports no changed existing signatures and
no newly added holes. All Lean lines are at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence`
(node `lem-cbc-proetale-extension-zero-comparison`).

Added 0 holes; split off 0 statements; 0 holes remain in the delivered module.
This is a proof, not a decomposition. Existing imported library declarations are
used as published; their independent obligations are not claimed as proved here.

## No longer needed

Removed proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: its instances are already exported
  by the actual constructions used here.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`: no slice-site
  module construction is used.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`: the fixed-coefficient
  source library already supplies the literal restriction functor and adjunction.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionByZeroAdjunction`: this slice-module
  adjunction is not the adjunction of the fixed-coefficient comparison in the statement.

Removed public reexports:

- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`:
  none of its legacy coherence lemmas is used; the upstream comparison import
  already exports the underlying pullback API.

- The public reexport of `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` is
  reduced to a proof-only import. The canonical comparison construction is
  already supplied upstream; the import is retained because the delivery base
  identifies this as a unit-route module. No unit-route module is bypassed.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`: its threefold
  coherence theorem is not needed. Its necessary reexports are replaced by the
  precise public imports of OpenImmersion.Comp, ModuleCat.AB and CompositionIso.

The following former proof dependencies are unnecessary for this proof:

- `lem-weil-pbc-etale-composition-cancellation`: open-immersion instances suffice.
- `lem-weil-proetale-weakly-etale-localization`: no change to a small skeleton or
  ringed slice site is required for the published fixed-coefficient restriction functor.
- `lem-weil-extension-by-zero-adjunction`: the recorded intrinsic/slice-module
  adjunction is unused; the upstream fixed-coefficient adjunction is already constructed.
- `def-pur-localized-ringed-site`: no ringed-site localization construction is used.

Retain `lem-cbc-extension-zero-composition` for its canonical composition
isomorphism, not its separate coherence theorem. Add the already proved
`lem-pc-adjunction-square-composition` as a proof dependency. No module file is
withdrawn. No blueprint unit realization is bypassed. The comparison node itself is retained,
and ProEtaleSiteComparison stays imported to preserve the unit route identified
by the delivery tool. The local compact-support unit record has no realized steps.

## Where the brief, the DAG or earlier work was wrong

The eight-step Hom-bijection plan can be implemented using existing conjugation
and pasting APIs instead of reconstructing those bijections. In particular,
`openImmersionLowerShriekComparisonUpperStarIso` already contains invertibility
and naturality. The substantive work is checking the exact composition and
identity normalizations in the statement.

The former pro-etale extension-adjunction dependency now records an intrinsic
constant-ring/slice-module interface, while this item's existing statement uses
`Sheaf (ProEt.topology X) (ModuleCat Λ)`. The original upstream fixed-coefficient
adjunction is exactly the one needed here; no conversion of module encodings is
needed. This delivery does not modify either encoding or weaken the statement.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
