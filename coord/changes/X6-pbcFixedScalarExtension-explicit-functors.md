# AlgebraicGeometry.ProEtale.pbcFixedScalarExtension

## Reason

Make the existing functor type or functor arguments explicit to prevent costly inference through derived functor compositions. These elaboration annotations preserve the construction and its inferred signature judgmentally. No target meaning changes.

## Old

```lean
noncomputable def pbcFixedScalarExtension {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) := (Sheaf.derivedRestrictScalars J φ).leftAdjoint
```

## New

```lean
noncomputable def pbcFixedScalarExtension {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} S)) :=
  (Sheaf.derivedRestrictScalars J φ).leftAdjoint
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.EtaleDerivedScalarTensor | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.EtaleProEtaleScalarMate | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteCoefficientDirectImage | C4 | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.NormalizedOriginComparisonCoherence | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.NormalizedOriginScalarComparisons | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.ProperOpenCoefficientMate | V3 | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.WitnessCompatibility | X6 | No adaptation: same functor and canonical comparison. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | M9 | No adaptation: same functor and canonical comparison. |

## Status

landed 20261020T221402-L-4181465 2026-10-20 (merge of deliver/X6/Sheaf.Paper.WitnessCompatibility)
