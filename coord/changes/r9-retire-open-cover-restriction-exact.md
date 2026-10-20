# AlgebraicGeometry.exactAt_over_of_open_cover

## Reason

The assigned Sheaf module has zero holes and no importers. Its complete theorem already
exists in WeilConjectures.AlgebraicGeometry.OpenCoverRestrictionExact, used by the adopted
KoszulRestrictionZeroBase module. Withdraw the unused Sheaf duplicate under brief step 8d
and attach its existing node to the source theorem. No adopted source file is changed.

## Old

The unused Sheaf.AlgebraicGeometry.OpenCoverRestrictionExact declares:

```lean
theorem exactAt_over_of_open_cover
    (X : Scheme.{u}) (K : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (ι : Type v) (V : ι → X.Opens) (U : X.Opens) (hU : U = ⨆ i, V i)
    (n : ℤ)
    (h : ∀ i, (((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) (V i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).ExactAt n) :
    (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).ExactAt n
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/OpenCoverRestrictionExact.lean via deleted.txt.
The landing tool leaves an empty module. The same theorem with the same signature,
including universes u and v, remains in the adopted source library at
lean/WeilConjectures/AlgebraicGeometry/OpenCoverRestrictionExact.lean.
The DAG attachment now records that existing source declaration.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.OpenCoverRestrictionExact
--uses AlgebraicGeometry.exactAt_over_of_open_cover` reports zero downstream modules.
A source search of all library Lean files finds no import of the withdrawn module.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OpenCoverRestrictionExact | R9 | Unused duplicate withdrawn. |
| WeilConjectures.AlgebraicGeometry.OpenCoverRestrictionExact | unclaimed | No change; retains the complete theorem. |
| WeilConjectures.AlgebraicGeometry.KoszulRestrictionZeroBase | unclaimed | No change; already imports the source module. |

No target signature or definition changes. No forced adaptations are needed.

## Status

landed 20261020T145537-L-2409585 2026-10-20 (merge of deliver/R9/Sheaf.AlgebraicGeometry.OpenCoverRestrictionExact)
