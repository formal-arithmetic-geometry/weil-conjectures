# DerivedCategory.traceExtendScalarsAdditive

## Reason

Restore the quarantined `Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws`
module and repair its public additivity instance. The archived body referred to
the removed identifier `ModuleCat.extendScalars_additive_sheaf`, so the module
failed to compile. The replacement uses the existing adjunction between scalar
extension and restriction: a left adjoint is additive, and its left functor is
`ModuleCat.extendScalars ρ`. The instance signature and all public statements are
unchanged; no target meaning changes.

## Old

```lean
noncomputable instance traceExtendScalarsAdditive {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) : (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
  ModuleCat.extendScalars_additive_sheaf ρ
```

## New

```lean
noncomputable instance traceExtendScalarsAdditive {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) : (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive
```

## Users

The module and its direct importers were quarantined together by the upstream
sync, so the current live source inventory has no importers. The restored public
instance remains available to any importer unchanged in name and type.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws | Q5 | Restored and repaired here |
| Sheaf.Paper.LocalFrobeniusConjugacy (quarantined) | unclaimed | Same public types; no adaptation |
| Sheaf.Paper.CondensedPointSupertrace (quarantined) | unclaimed | Same public types; no adaptation |
| Sheaf.Paper.LocalWeilModelTraceIndependence (quarantined) | unclaimed | Same public types; no adaptation |

`tools/downstream.py` reports unknown module for both the short and qualified
instance name because this item is absent from the live source tree. A scan of
both `lean/` and `quarantine/` finds no explicit uses of the instance name outside
its definition and finds the three archived direct importers listed above. The
instance proves a proposition, so replacing its proof cannot change the meaning
of the scalar-extension functor or the inferred homotopy functor. The complete
restored module compiles cleanly. No consumer is modified in this packet.

## Status

landed 20261020T230825-L-617471 2026-10-20 (merge of deliver/Q5/Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws)
