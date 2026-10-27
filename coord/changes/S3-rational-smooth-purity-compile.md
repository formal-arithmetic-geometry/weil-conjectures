# WeilConjectures.RationalSmoothPurityCanonical.ordinaryLeftUnitor

## Reason

Keep the ordinary monoidal presentation abstract during elaboration of the
canonical purity trace. The baseline file exceeded the fixed 60-second limit.
The new `ordinaryMonoidal` cache depends only on the prime, coefficient field,
and scheme. At `P.coefficients.l` and `P.extension` it is exactly
`(ordinaryClosed P T).monoidal`, with its integral derived category explicit.
Its tensor API is checked at the same general coefficient parameters. The coefficient-unit and tensor
presentation types are definitionally equal to their old types, by unfolding
`ordinaryMonoidal` and `CoefficientClosedStructure.tensor`. No target changes.

Keep the completion/unit and ambient pullback/tower presentation definitions
abstract locally. These are elaboration controls on the same standard
localizations and normalized morphisms.

## Old

```lean
def ordinaryCoefficientUnit (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) :
    (twist P T aT 0).obj ≅
      (ordinaryClosed P T).monoidal.tensorUnit := by
  unfold ordinaryClosed
  exact (shiftFunctorZero _ ℤ).app _ ≪≫
    (@RingedSiteDualityModel.unitIso.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension T none)).symm

theorem ordinaryTensor_eq (T : Scheme.{u}) :
    (ordinaryModel P.coefficients.l P.extension T).tensor = (ordinaryClosed P T).tensor := by
  exact (ordinaryModel_existsUnique P.coefficients.l P.extension T).exists.choose_spec.1

def ordinaryLeftUnitor
    (K : DerivedCategory (integralTowerModules P.coefficients.l P.extension Y)) :
    (ordinaryModel P.coefficients.l P.extension Y).tensor.obj
      ((twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj,K) ≅ K :=
by
  exact tensorLeftUnitorFromPresentation (ordinaryClosed P Y).monoidal
    (ordinaryModel P.coefficients.l P.extension Y).tensor (ordinaryTensor_eq P Y) _ K
    (ordinaryCoefficientUnit P Y (Y ↘ Spec (.of P.field.k)))
```

## New

```lean
def ordinaryMonoidal (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) : MonoidalCategory (DerivedCategory (integralTowerModules l E T)) :=
  (@RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
    _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
    (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
    (IntegralOnSlice.duality.{u, u} l E T none)).monoidal

private theorem ordinaryMonoidal_tensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) :
    (ordinaryModel l E T).tensor = @MonoidalCategory.tensor _ _ (ordinaryMonoidal l E T) := by
  unfold ordinaryModel ordinaryMonoidal
  exact (ordinaryModel_existsUnique l E T).exists.choose_spec.1

def ordinaryCoefficientUnit (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) :
    (twist P T aT 0).obj ≅
      (ordinaryMonoidal P.coefficients.l P.extension T).tensorUnit := by
  unfold ordinaryMonoidal
  exact (shiftFunctorZero _ ℤ).app _ ≪≫
    (@RingedSiteDualityModel.unitIso.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension T none)).symm

theorem ordinaryTensor_eq (T : Scheme.{u}) :
    (ordinaryModel P.coefficients.l P.extension T).tensor =
      @MonoidalCategory.tensor _ _ (ordinaryMonoidal P.coefficients.l P.extension T) := by
  exact ordinaryMonoidal_tensor P.coefficients.l P.extension T

def ordinaryLeftUnitor
    (K : DerivedCategory (integralTowerModules P.coefficients.l P.extension Y)) :
    (ordinaryModel P.coefficients.l P.extension Y).tensor.obj
      ((twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj,K) ≅ K :=
by
  exact tensorLeftUnitorFromPresentation (ordinaryMonoidal P.coefficients.l P.extension Y)
    (ordinaryModel P.coefficients.l P.extension Y).tensor
    (ordinaryTensor_eq P Y) _ K
    (ordinaryCoefficientUnit P Y (Y ↘ Spec (.of P.field.k)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalSmoothPurityCanonical | S3 | Uses the same monoidal structure through its cached presentation. |

`tools/downstream.py --uses` lists only this module for each of
`ordinaryCoefficientUnit`, `ordinaryTensor_eq`, and `ordinaryLeftUnitor`.
No external consumer needs adaptation. The other downstream modules use the
unchanged canonical purity interfaces. The wrapper does not change their meaning.

## Status

landed 20261026T070945-L-3715061 2026-10-26 (merge of deliver/S3/Sheaf.Paper.RationalSmoothPurityCanonical)
