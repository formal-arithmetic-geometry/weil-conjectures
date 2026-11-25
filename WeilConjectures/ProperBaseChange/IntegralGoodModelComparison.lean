/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProperIntegralOrdinaryData

/-! # Ordinary comparison on good integral representatives

On good integral representatives, the derived pullback followed by the coefficient transport
is computed by the strict pullback complex followed by the strict coefficient transport.

## Main results

- `pbc_integral_good_model_comparison`

## Implementation details

The comparison is obtained by whiskering the ordinary good-model comparison by the coefficient
transport, and the exact coefficient factorization by the strict pullback complex functor; its
components are the composites of the two comparison components.

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, Remark 6.8.15
- [Stacks, Tag 06YY]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] integralDerivedPullback pbcIntegralDatum
  integralDetailedCoefficientComparison Functor.mapDerivedCategory HasDerivedCategory.standard
  integralDerivedPullbackComparison pbcIntegralDetailedTransportFactors

private def rightAssoc3
    {A B C D E : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (F0 : A ⥤ B)
    (F1 : B ⥤ C)
    (F2 : C ⥤ D)
    (F3 : D ⥤ E) :
    (F0 ⋙ F1 ⋙ F2) ⋙ F3 ≅ F0 ⋙ F1 ⋙ F2 ⋙ F3 :=
  Functor.associator F0 (F1 ⋙ F2) F3 ≪≫
    Functor.isoWhiskerLeft F0 (Functor.associator F1 F2 F3)

@[simp]
private theorem rightAssoc3_hom_app
    {A B C D E : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (F0 : A ⥤ B)
    (F1 : B ⥤ C)
    (F2 : C ⥤ D)
    (F3 : D ⥤ E) (X : A) :
    (rightAssoc3 F0 F1 F2 F3).hom.app X = 𝟙 _ := by
  simp [rightAssoc3]

private def ordinaryGoodComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T) :
    integralOperationsGoodLocalization l E T ⋙ integralDerivedPullback l E h ⋙
        integralDetailedTransport U l E ≅
      (integralOperationsGoodComplex l E T).ι ⋙ integralOperationsPullbackComplexFunctor l E h ⋙
        pbcIntegralTransportComplex U l E ⋙ DerivedCategory.Q := by
  let J := (integralOperationsGoodComplex l E T).ι
  let L := integralOperationsGoodLocalization l E T
  exact (Functor.associator L (integralDerivedPullback l E h)
      (integralDetailedTransport U l E)).symm ≪≫
    Functor.isoWhiskerRight (integralDerivedPullbackComparison l E h)
      (integralDetailedTransport U l E) ≪≫
    rightAssoc3 J (integralOperationsPullbackComplexFunctor l E h) DerivedCategory.Q
      (integralDetailedTransport U l E) ≪≫
    Functor.isoWhiskerLeft J
      (Functor.isoWhiskerLeft (integralOperationsPullbackComplexFunctor l E h)
        (pbcIntegralDetailedTransportFactors U l E))

private theorem ordinaryGoodComparison_hom_app
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T)
    (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
    (ordinaryGoodComparison l E h).hom.app P =
      (integralDetailedTransport U l E).map
          ((integralDerivedPullbackComparison l E h).hom.app P) ≫
        (pbcIntegralDetailedTransportFactors U l E).hom.app
          ((integralOperationsPullbackComplexFunctor l E h).obj P.obj) := by
  simp only [ordinaryGoodComparison, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, rightAssoc3_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp]
  erw [Category.id_comp]
  rfl

/-- On good representatives, the derived pullback along `h` followed by the coefficient
transport is isomorphic to the strict pullback complex followed by the strict coefficient
transport, with components the composite of the derived pullback comparison and the
coefficient transport factorization. -/
theorem pbc_integral_good_model_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T) :
    ∃ e₀ : integralOperationsGoodLocalization l E T ⋙ integralDerivedPullback l E h ⋙
          integralDetailedTransport U l E ≅
        (integralOperationsGoodComplex l E T).ι ⋙ integralOperationsPullbackComplexFunctor l E h ⋙
          pbcIntegralTransportComplex U l E ⋙ DerivedCategory.Q,
      ∀ P : (integralOperationsGoodComplex l E T).FullSubcategory,
        e₀.hom.app P = (integralDetailedTransport U l E).map
            ((integralDerivedPullbackComparison l E h).hom.app P) ≫
          (pbcIntegralDetailedTransportFactors U l E).hom.app
            ((integralOperationsPullbackComplexFunctor l E h).obj P.obj) := by
  exact ⟨ordinaryGoodComparison l E h, ordinaryGoodComparison_hom_app l E h⟩

end WeilConjectures
