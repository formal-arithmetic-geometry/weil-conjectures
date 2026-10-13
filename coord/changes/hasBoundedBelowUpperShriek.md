# AlgebraicGeometry.Etale bounded-below exceptional inverse image

## Reason

The prior delivery proved a mathematically false bounded-below instance by ex falso from the
disputed strictification interface. The assertion fails for arbitrary compactifiable morphisms
with disconnected schemes of unbounded fibre dimensions.

## Old

```lean
instance hasBoundedBelowUpperShriek (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f where
  plus_rightDerivedUpperShriek_obj := sorry

instance hasBoundedBelowUpperShrieks (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    HasBoundedBelowUpperShrieks (ModuleCat.{u + 1} Λ) where
  hasBoundedBelowUpperShriek _ _ := inferInstance
```

## New

The two false torsion-coefficient instances are removed; the general classes retain their existing signatures.

## Users

| module | group holding it | effect |
|---|---|---|
| `WeilConjectures` | unclaimed | direct importer; no bounded-below declaration use and no forced adaptation |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions` | unclaimed | direct importer; no bounded-below declaration use and no forced adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | direct importer; uses adjunction declarations only, with no forced adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.Dualizing` | unclaimed | direct importer; no bounded-below declaration use and no forced adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.Localization` | unclaimed | direct importer; uses adjunction declarations only, with no forced adaptation |
| `WeilConjectures.SixFunctors.Etale.Derived.Shift` | unclaimed | direct importer; uses adjunction declarations only, with no forced adaptation |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek` | unclaimed | direct importer; retains its existing explicit `[Etale.HasBoundedBelowUpperShriek A f]` hypotheses, with no forced adaptation |

## Status

landed 20261013T190151-L-3220102 2026-10-13 (merge of deliver/P3/WeilConjectures.SixFunctors.Etale.Derived.UpperShriek)
