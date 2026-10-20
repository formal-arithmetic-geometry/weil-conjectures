# SupportedDerivedScalarUnit

## Reason

Use the same named canonical exact degree-zero scalar unit as the coefficient comparison.
Its general-site specialization fixes the derived-category data before a scheme is supplied.
This removes expensive localization-data conversions from the universal-property
bridge. `SheafExactDegreeZero.scalarUniversal_iff` proves equivalence with the old raw
formula, including all unbounded test objects. The change is representational;
there is no extra flatness, finiteness, boundedness or other hypothesis.

The module also selects `scalarWeakSheafify` as a local instance for elaborating
the unchanged constant-generator clauses. This is the existing proved
`HasSheafify.isRightAdjoint`; proof irrelevance preserves the sheafification data.

## Old

```lean
@[irreducible]
def SupportedDerivedScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) : Prop :=
  ∀ K : DerivedCategoryModule S T,
    Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj G ⟶ K ↦
      (DerivedCategory.singleFunctor _ 0).map η ≫
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).inv.app
          G ≫
          (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategory.map f)
```

## New

```lean
@[irreducible]
def SupportedDerivedScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) : Prop :=
  SheafExactDegreeZero.scalarUniversal T.smallEtaleTopology φ F G η
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar --uses
SupportedDerivedScalarUnit` found 654 transitive importers and these two textual
users. Their mathematical statements are unchanged by `universal_iff`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar | unclaimed | SupportedKummerScalar retains exactly the same derived universal-property condition. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarSource | D3 | Its normalized units retain exactly their old unbounded universal properties; no source edit is required. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | M9 | New proof consumer: identifies the normalized source unit and cancels its universal property. |

Targets whose meaning depends on the predicate are submitted to the usual
statement-meaning re-review. No forced adaptations are included.

## Status

landed 20261020T230814-L-615093 2026-10-20 (merge of deliver/M9/Sheaf.SixFunctors.GeoCartierCoeffExtension)
