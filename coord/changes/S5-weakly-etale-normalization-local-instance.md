# weaklyEtale_normalization_tensor

## Reason

The proof locally enables `Algebra.TensorProduct.rightAlgebra` so the generic
localization and tensor-normalization helpers use the intended D-algebra structure.
The preflight conservatively treats an added attribute command as a visible change.
The attribute is explicitly local and expires at the existing section end.
No public import, declaration signature, definition, instance or attribute is exported
by this change. No target statement or definition used by a target changes.

## Old

No local instance attribute command. The public signature is:

```lean
theorem weaklyEtale_normalization_tensor
    (C : Type u) [CommRing C] [IsNoetherianRing C] (hCuc : IsUniversallyCatenary C)
    [IsLocalRing C] [IsDomain C]
    [Module.Finite C (integralClosure C (FractionRing C))]
    (D : Type v) [CommRing D] [IsNoetherianRing D] [IsLocalRing D]
    [Algebra C D] [IsLocalHom (algebraMap C D)] [Algebra.WeaklyEtale C D] :
    IsReduced D ∧
      (∃ e : @AlgEquiv D
        (TensorProduct C (integralClosure C (FractionRing C)) D)
        (integralClosure D (Localization (nonZeroDivisors D))) _ _ _
        (Algebra.TensorProduct.rightAlgebra) (inferInstance),
        ∀ (c : integralClosure C (FractionRing C)) (a s : C), s ≠ 0 →
          algebraMap C (FractionRing C) s * c.val = algebraMap C (FractionRing C) a →
          ∀ d : D,
            algebraMap D (Localization (nonZeroDivisors D)) (algebraMap C D s) *
                (e (c ⊗ₜ[C] d)).val =
              algebraMap D (Localization (nonZeroDivisors D)) (algebraMap C D a * d)) ∧
      ∀ (P : Ideal D), P ∈ Ideal.minimalPrimes (⊥ : Ideal D) →
        ∃ (F : CommRingCat.{v}) (A : Algebra D F),
          ∃ (e : @AlgEquiv D
            (integralClosure D (Localization (nonZeroDivisors D)))
            ((integralClosure (D ⧸ P) (FractionRing (D ⧸ P))) × F)
            _ _ _
            inferInstance
            (RingHom.toAlgebra
              (RingHom.prod
                ((@algebraMap (D ⧸ P) (integralClosure (D ⧸ P) (FractionRing (D ⧸ P))) _ _
                  (SubalgebraClass.toAlgebra (integralClosure (D ⧸ P) (FractionRing (D ⧸ P))))).comp
                  (Ideal.Quotient.mk P))
                (@algebraMap D F _ _ A)))),
            ∀ (d : D),
              (e (algebraMap D (integralClosure D (Localization (nonZeroDivisors D))) d)).1 =
                (@algebraMap (D ⧸ P) (integralClosure (D ⧸ P) (FractionRing (D ⧸ P))) _ _
                  (SubalgebraClass.toAlgebra (integralClosure (D ⧸ P) (FractionRing (D ⧸ P)))))
                  (Ideal.Quotient.mk P d)
```

## New

The public signature above is unchanged verbatim. Before the private proof helpers:

```lean
attribute [local instance] Algebra.TensorProduct.rightAlgebra
```

All added helpers are private proved theorems. All added imports are proof imports.

## Users

The direct consumer `Sheaf.RingTheory.WeaklyEtaleLocalComponentDimension` calls the
theorem with explicit structures and still installs `rightAlgebra` locally where needed.
Its existing call and statements need no adaptation. Its unchanged source compiled
against the repaired module in the diagnostic overlay in 16.0 seconds with no warnings. The current downstream scan
finds 15 transitive importers, listed below; their statements and definitions are
unchanged because the public interface and public import closure are unchanged.
The direct declaration-use scan names only this item and its direct consumer.
No consumer module is edited. No target statement review is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AlterationRelativeCurvePreparation | Not adapted | Interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair | Not adapted | Interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericSmoothBoundaryPreparation | Not adapted | Interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyIntegralCurveFactorization | Not adapted | Interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeCurveFactorization | Not adapted | Interface preserved; no adaptation. |
| Sheaf.RingTheory.ExcellentOfWeaklyEtale | Not adapted | Interface preserved; no adaptation. |
| Sheaf.RingTheory.FieldAlgebraStrictHenselizationExcellent | Not adapted | Interface preserved; no adaptation. |
| Sheaf.RingTheory.IsExcellentFiniteTypeLocalization | Not adapted | Interface preserved; no adaptation. |
| Sheaf.RingTheory.LocallyNagataCatenaryOfWeaklyEtale | Not adapted | Interface preserved; no adaptation. |
| Sheaf.RingTheory.PuncturedCurveBranches | Not adapted | Interface preserved; no adaptation. |
| Sheaf.RingTheory.WeaklyEtaleLocalComponentDimension | Not adapted | Interface preserved; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.FiniteEtaleMarkingSections | Not adapted | Interface preserved; no adaptation. |
| Sheaf.TraceFormula.ProjectiveInseparableSpreadNormalization | Not adapted | Interface preserved; no adaptation. |
| Sheaf.TraceFormula.RelativeCompletionEtaleApproximation | Not adapted | Interface preserved; no adaptation. |
| Sheaf.TraceFormula.ValuationRankOneFormalComparison | Not adapted | Interface preserved; no adaptation. |

## Status

landed 20261020T135425-L-1821844 2026-10-20 (merge of deliver/S5/Sheaf.RingTheory.WeaklyEtaleNormalization)
