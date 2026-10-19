# AlgebraicGeometry.ProEtale.finiteCoefficientRealization_full_faithful_essSurj

## Reason

Sheaf.Paper.RefinementCoefficientRealization was unclaimed when edited. This is a dependency used by the assigned comparison
proof. The existing ring-general realization equivalence already proves all three clauses. Use its Full, Faithful and EssSurj instances; retain the statement and public imports.

## Old

```lean
theorem finiteCoefficientRealization_full_faithful_essSurj (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientRealization T Λ).Full ∧
      (finiteCoefficientRealization T Λ).Faithful ∧
        (finiteCoefficientRealization T Λ).EssSurj
```

The proof was `by sorry`.

## New

```lean
theorem finiteCoefficientRealization_full_faithful_essSurj (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientRealization T Λ).Full ∧
      (finiteCoefficientRealization T Λ).Faithful ∧
        (finiteCoefficientRealization T Λ).EssSurj := by
  let := finiteCoefficientRealizationIsEquivalenceRing T Λ
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Realization gives the coefficient equivalence used for canonical transport.
Source: blueprint finite coefficient modules, order 1233
(blueprint: def-weil-pbc-proetale-modules). -/
instance refinementRealizationIsEquivalence (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientRealization T Λ).IsEquivalence where
  full := (finiteCoefficientRealization_full_faithful_essSurj T Λ).1
  faithful := (finiteCoefficientRealization_full_faithful_essSurj T Λ).2.1
  essSurj := (finiteCoefficientRealization_full_faithful_essSurj T Λ).2.2
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageFormula | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle | T9 | Same signature and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.Paper.AdicTorFlatCohomology | S6 | Same signature and visibility; no adaptation. |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | M7 | Same signature and visibility; no adaptation. |
| Sheaf.Paper.RefinementComparisonIsomorphism | unclaimed | Same signature and visibility; no adaptation. |

All public signatures and public imports are identical. No definition or target changes.
No forced adaptation is included.

## Status

landed 20261019T005336-L-2754480 2026-10-19 (merge of deliver/K7/Sheaf.AlgebraicGeometry.UnboundedSiteComparison)
