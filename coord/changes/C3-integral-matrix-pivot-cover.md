# integralMatrix_pivot_cover

## Reason

Replace the pivot-cover hole by a real block-assembly proof and isolate the strictly
analytic cover construction. Expose reusable, proved internal-module APIs for continuous
multipliers and scalar extension. No existing declaration signature changes.

## Old

`Sheaf.Paper.IntegralMatrixPivotCover` contained `integralMatrix_pivot_cover := by sorry`.
The seven helper modules added by this delivery were absent. The original theorem signature is unchanged:

```lean
theorem integralMatrix_pivot_cover (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] :
  ∀ (n : ℕ) (X : Scheme.{u})
    (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) (a : A ⟶ B),
    Nonempty (A ≅ Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n) →
    Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) B →
    (∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) →
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      let R := condensedRingObj (integralCoeff ℓ E) (V.X k)
      let T := (ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (V.f k)))
      T.map a = 0 ∨
        ∃ (m : ℕ), m < n ∧
          ∃ (A₁ B₁ : Mod (Sheaf (Scheme.ProEt.topology (V.X k)) Ab.{u + 1}) R)
            (_ : A₁ ≅ Mod.finiteFree R m),
            Mod.IsFree R B₁ ∧
              ∃ (p : Mod.regular R ⟶ Mod.regular R), Mono p ∧
                IsIso ((Mod.extendScalars
                  (coefficientMap (integralScalarMap ℓ E) (V.X k))).map p) ∧
                ∃ (r : A₁ ⟶ Mod.regular R) (c : Mod.regular R ⟶ B₁) (d : A₁ ⟶ B₁)
                  (eA : T.obj A ≅ Mod.regular R ⊞ A₁)
                  (eB : T.obj B ≅ Mod.regular R ⊞ B₁),
                  eA.inv ≫ T.map a ≫ eB.hom =
                    biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d)
```

## New

The same theorem first reduces arbitrary free modules to a map between standard finite
free modules and transports its rational cokernel cover through the cokernel isomorphism.
It is then proved from `integralMatrix_analytic_cover`,
`integralMatrix_entry_properties`, and `finiteBiproduct_pivot`. The latter two are fully
proved. The actual coefficient functions and scalar inclusion are defined in
`IntegralMatrixAnalyticCover`; it also explicitly constructs the standard normalized
pullback bases. Its analytic cover theorem is the sole new hole and supplies no basis
or coefficient realization data.
`ContinuousRegularFunctions`, `RegularExtensionComparison`, and
`IntegralRegularRationalUnit` supply the proved APIs used by the entry calculation.
`ContinuousCoefficientRealizations` constructs canonical monoid comparisons and proves
their isomorphism and naturality. The analytic cover uses this canonical realization.
All existing statements, including the five targets, keep identical signatures.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralMatrixPivotCover | C3 | Same signature; proof and private imports change. |
| Sheaf.Paper.IntegralConstructibleKernels | unmodified | Uses the same pivot-cover statement. |
| Sheaf.Paper.ContinuousCoefficientRealizations | new in C3 delivery | Canonical coefficient maps and compatibility. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | new in C3 delivery | Constructs matrix functions and normalized bases; states analytic charts. |
| Sheaf.Paper.ContinuousRegularFunctions | new in C3 delivery | Actual sectionwise multiplier API. |
| Sheaf.Paper.RegularExtensionComparison | new in C3 delivery | Actual adjunction comparison and naturality. |
| Sheaf.Paper.IntegralRegularRationalUnit | new in C3 delivery | Uses function and extension comparisons. |
| Sheaf.Paper.IntegralMatrixEntryProperties | new in C3 delivery | Uses compatible analytic data and proved scalar APIs. |
| Sheaf.Paper.FiniteBiproductPivot | new in C3 delivery | Generic categorical block assembly. |

No existing module is adapted, and no target definition changes. The additions are
reviewable interfaces; downstream imports retain the original pivot-cover statement.

## Status

landed 20261016T043121-L-2930597 2026-10-16 (merge of deliver/C3/Sheaf.Paper.IntegralMatrixPivotCover)
