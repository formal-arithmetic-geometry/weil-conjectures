# AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp

## Reason

Make the existing functor type or functor arguments explicit to prevent costly inference through derived functor compositions. These elaboration annotations preserve the construction and its inferred signature judgmentally. No target meaning changes.

## Old

```lean
noncomputable def pbcFixedScalarExtensionComp {R S V : Type (u + 1)}
    [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ) :
    pbcFixedScalarExtension J φ ⋙ pbcFixedScalarExtension J ψ ≅ pbcFixedScalarExtension J χ :=
  Adjunction.leftAdjointCompIso (Adjunction.ofIsRightAdjoint _)
    (Adjunction.ofIsRightAdjoint _) (Adjunction.ofIsRightAdjoint _)
    (Sheaf.derivedRestrictScalarsCompIso J h)
```

## New

```lean
noncomputable def pbcFixedScalarExtensionComp {R S V : Type (u + 1)}
    [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ) :
    pbcFixedScalarExtension J φ ⋙ pbcFixedScalarExtension J ψ ≅ pbcFixedScalarExtension J χ :=
  Adjunction.leftAdjointCompIso
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J ψ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J χ))
    (Sheaf.derivedRestrictScalarsCompIso J h)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.ExceptionalCoefficientComparison | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteCoefficientDirectImage | C4 | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.NormalizedOriginComparisonCoherence | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.NormalizedOriginScalarComparisons | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.Paper.WitnessCompatibility | C1 | No adaptation: same functor and canonical comparison. |
| Sheaf.SixFunctors.EtaleOpenScalarCoherence | K3 | No adaptation: same functor and canonical comparison. |
| Sheaf.SixFunctors.EtaleOpenTensor | K3 | No adaptation: same functor and canonical comparison. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | No adaptation: same functor and canonical comparison. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | M9 | No adaptation: same functor and canonical comparison. |

## Status

landed 20261021T003502-L-1642808 2026-10-21 (merge of deliver/C1/Sheaf.Paper.WitnessCompatibility)
