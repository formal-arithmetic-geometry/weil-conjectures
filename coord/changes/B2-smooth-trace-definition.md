# AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace

## Reason

The quarantined source left `smoothTrace` as a `sorry` inside a definition.  Stage 3
requires a concrete definition.  The source signature is retained, including its
unconditional elaboration; the smooth branch now takes the unique representing trace
from `existsUnique_smoothTrace`, while the nonsmooth extension is the zero morphism.

## Old

```lean
noncomputable def smoothTrace :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
      (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶
      𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) := by
  sorry
```

## New

```lean
noncomputable def smoothTrace :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
      (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶
      𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) := by
  classical
  exact if h : Nonempty (SmoothOfRelativeDimension d f.left) then
    (existsUnique_smoothTrace ℓ f d h.some
      (boundedConstructibleTateTwist ℓ X d (2 * d)) (Iso.refl _)
      (MonoidalCategoryStruct.tensorUnit
        (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) rfl).choose
  else
    0
```

## Users

| Module | Group holding it | Effect |
| --- | --- | --- |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Uses the same public trace signature. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Uses the same public trace signature. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Imports and uses `smoothTrace`. |
| Sheaf.Targets.SmoothPurityQbarTargetsCheck | unclaimed | Checks the trace-based target route. |
| WeilConjectures | unclaimed | Aggregates the source module. |

## Status

landed 20261027T205753-L-1613179 2026-10-27 (merge of deliver/B2/WeilConjectures.SmoothPurity.Defs)
