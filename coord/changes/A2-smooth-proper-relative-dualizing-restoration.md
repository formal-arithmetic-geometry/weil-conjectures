# AlgebraicGeometry.smoothProper_dualizing

## Reason

Restore the assigned quarantined module and repair its obsolete determinant-evaluation
import. The rework row records an unknown identifier after retirement of the duplicate
Sheaf module. The adopted theorem uses exteriorPower, whereas the preserved public
statement and diagonal evaluation use exteriorSheaf. Transport the adopted evaluation
through exteriorSheafPowerIso, the single functor, the opposite shifts, and tensor.
The final cancellation by associator and unitors remains the preserved argument.

## Old

The signature in the quarantine archive is:

```lean
theorem smoothProper_dualizing
    (X S : Scheme.{u}) [CompactSpace S] [IsLocallyNoetherian S]
    (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory S)
    (comparison : R ⋙ (schemeDerivedQCohProperty S).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ a) (O : schemeDerivedQCohCategory S)
    (hO : O.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings S.toRingedSpace))) :
    Nonempty ((a.obj O).obj ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorSheaf f.relativeDifferentials d))⟦(d : ℤ)⟧)
```

Its proof imported Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation and called
shiftedDeterminant_dual_evaluation as though it still used exteriorSheaf.

## New

The signature above is preserved verbatim, with the same universes, instances,
visibility and public imports. The private proof imports now use
WeilConjectures.AlgebraicGeometry.ShiftedDeterminantDualEvaluation and
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison. The two comparisons
are mapped through single and shifts, then tensored and composed with the adopted
evaluation. No shared definition, statement, instance or attribute changes.
The quarantine archive and all mathematical dependencies are retained.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | A2 | Restored; obsolete proof call repaired. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | quarantined; no active claim found | Existing signature and public imports preserved; no adaptation needed. |

The active downstream.py scan reports zero importers. The quarantine scan finds
SmoothProperCurveDualizing, which calls the same unchanged theorem. No consumer
signature or public proof environment changes, so no forced adaptations are made.
The comparison is uniform for d=0 and the empty scheme, and the independent derived
universes wX and wS remain unrestricted. The unit route is unchanged.

Validation: the complete restored module compiled without warnings in 3.8 seconds
through lcompile.py. Delivery preflight performs the declaration and axiom probes.
There are zero direct holes before and after, and zero new holes.

## Status

landed 20261026T100207-L-4142021 2026-10-26 (merge of deliver/A2/Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing)
