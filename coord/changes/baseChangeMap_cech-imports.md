# AlgebraicGeometry.baseChangeMap_cech (module exports)

## Reason

The literal signature is proved using the derived-pullback counit and the
canonical base-change definition, not Cech-resolution or direct-image-composition
lemmas. Remove redundant public imports; explicitly import the two Mathlib
morphism properties used in the unchanged signature. The existing unused gamma
binder requires a scoped unused-variable linter option; this does not alter the
elaborated type. The mismatch with the stronger source statement is explained in
the report and needs independent statement review.

## Old

The original exported-import interface, verbatim:

```lean
module

public import Sheaf.AlgebraicGeometry.CechResolution
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedAdjoint
public import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Mathlib.Algebra.Homology.Homotopy
```

The theorem's signature is unchanged (the report and module contain it in full).
The original declaration had no scoped linter option.

## New

```lean
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
```

A scoped `set_option linter.unusedVariables false in` surrounds the existing
declaration. It silences its unused existential gamma and cover hypotheses;
no declarations, notation, instances, definitions or theorem signatures change.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BaseChangeMapCech | B2 | Proof completed, public imports reduced; signature identical. |
| Sheaf.AlgebraicGeometry.AffineRelativelyFlatCanonicalModuleBaseChange | unclaimed (local claims snapshot); no edit | Imports BaseChangeMapCech only for proofs and CechResolution independently; unchanged statement and proof. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange | unclaimed (local claims snapshot); no edit | Imports BaseChangeMapCech only for proofs and CechResolution independently; unchanged statement and proof. |

`tools/downstream.py ... --uses AlgebraicGeometry.baseChangeMap_cech` reports only
the declaration's own module as a textual user. The two current immediate importers are
listed additionally above. The earlier direct importer
RelativelyFlatCanonicalModuleBaseChange now imports the affine result instead. Both import the changed module non-publicly, so
removed public exports do not propagate to their importers. The retained
DerivedModuleBaseChangeMap publicly supplies the definitions used in the
signature. There are no forced adaptations and no target statement changes.
No removed declaration is assumed globally unnecessary: the report distinguishes
formal pruning here from missing source-level obligations.

## Status

landed 20261012T152346-L-2312572 2026-10-12 (merge of deliver/B2/Sheaf.AlgebraicGeometry.BaseChangeMapCech)
