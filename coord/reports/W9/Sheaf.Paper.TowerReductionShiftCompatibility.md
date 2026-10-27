## What changed

Proved `AlgebraicGeometry.ProEtale.sp_tower_reduction_shift_compatibility` from the
existing `SpCoefficientTowersAbelian.reduction_rep` normalization. Three proved
private helpers establish termwise shift compatibility of ordinary natural
transformations, compose the represented reduction with the exact evaluation
factors and scalar counit, and descend shift compatibility through localization.
The scalar counit's compatibility is the `choose_spec` of exactly the coherent
right Kan shift used by `spTowerScalarShift`.

The public statements, definitions and public imports are retained. Removed five unused
private proof imports. Updated the item's node proof, proof dependencies and
proof origin to describe the Lean argument. No other modules are adapted. The complete module compiled cleanly through
`lcompile.py` in 18.7 seconds, with no diagnostics.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.ProEtale.sp_tower_reduction_shift_compatibility`
(node `lem-sp-tower-reduction-shift-compatibility`). No holes added, no split-off
statements, and zero holes remain in the delivered module. This is a proof from
existing declared dependencies, not a decomposition.

## No longer needed

Removed private proof imports:

- `Sheaf.Paper.SemilinearSystemModels` (`def-coef-semilinear-system-models`): the
  actual ordinary natural reduction and its full representative formula are
  already fields of the tower datum.
- `Sheaf.Algebra.Homology.SheafRingDerivedHomComparison`
  (`lem-pur-sheaf-ring-derived-hom-comparison`): no new adjunction transpose
  calculation is needed after `reduction_rep`.
- `Sheaf.Paper.RingedCoefficientScalarShifts`
  (`lem-pur-coefficient-scalar-shifts`): use the recorded generic coherent right
  Kan shift theorem directly, at the actual cochain counit, as the definition
  `spTowerScalarShift` already does.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: its ordinary-module
  presentation is unused. The actual ringed-site cochain model remains available
  through the tower data and is used; `lem-pur-derived-change-of-rings` therefore
  stays a proof dependency.
- `Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic`: only
  `Localization.natTrans_ext` is needed, already available through the existing
  imports. The localization dependency stays in the node.

The explicit pure-tensor calculation is unnecessary: the ordinary reduction is
already a natural transformation between additive functors, and termwise shift
compatibility follows degree by degree from its components. Thus
`sk-def-sp-coefficient-towers` is needed for the statement but no longer separately
for that proof step. No entire library module is withdrawn or claimed globally
unreachable, and the unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The DAG's representative formula is already supplied by the current Lean tower
interface. Its additional Hom-comparison calculation can be omitted. Its
coefficient-scalar-shifts declaration uses a different presentation; applying the
underlying `rightKanExtension_coherentShift` theorem directly matches the precise
cochain comparison and chosen shift of this item.

The proof treats all integer shifts uniformly, including zero and negative shifts,
and includes equal levels and the empty scheme. It never inverts the scalar
counit and introduces no flatness, boundedness or constructibility condition.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
