/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinducedComplexes
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceExactProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Derived comparison for the first coinduced product

Source: Stacks Tags 0941 and 079P.
(blueprint: lem-coef-sequence-product-derived-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CoefficientCoinduction

section ProductComparison

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [HasCountableProducts A]
  [HasExactLimitsOfShape (Discrete ℕ) A]
  [HasCountableProducts (DerivedCategory A)]
  {B : ℕ → Type*} [∀ n, Category (B n)] [∀ n, Abelian (B n)]
  [∀ n, HasDerivedCategory (B n)]
  (F : ∀ n, A ⥤ B n) (G : ∀ n, B n ⥤ A)
  [∀ n, (F n).Additive] [∀ n, (G n).Additive]
  [∀ n, PreservesFiniteLimits (F n)] [∀ n, PreservesFiniteColimits (F n)]
  [∀ n, PreservesFiniteLimits (G n)] [∀ n, PreservesFiniteColimits (G n)]

private theorem localized_product_comparison (adj : ∀ n, F n ⊣ G n)
    (K : CochainComplex A ℤ) :
    ∃ a : DerivedCategory.Q.obj (∏ᶜ fun n ↦
        ((G n).mapHomologicalComplex (.up ℤ)).obj
          (((F n).mapHomologicalComplex (.up ℤ)).obj K)) ≅
      ∏ᶜ fun n ↦ (G n).mapDerivedCategory.obj
        ((F n).mapDerivedCategory.obj (DerivedCategory.Q.obj K)),
      DerivedCategory.Q.map (Pi.lift (fun n ↦
        ((adj n).mapHomologicalComplex (.up ℤ)).unit.app K)) ≫ a.hom =
      Pi.lift (fun n ↦ (adj n).mapExactDerivedCategory.unit.app
        (DerivedCategory.Q.obj K)) := by
  let L (n : ℕ) := ((G n).mapHomologicalComplex (.up ℤ)).obj
    (((F n).mapHomologicalComplex (.up ℤ)).obj K)
  let D (n : ℕ) := (G n).mapDerivedCategory.obj
    ((F n).mapDerivedCategory.obj (DerivedCategory.Q.obj K))
  let e (n : ℕ) : D n ≅ DerivedCategory.Q.obj (L n) :=
    (G n).mapDerivedCategory.mapIso ((F n).mapDerivedCategoryFactors.app K) ≪≫
      (G n).mapDerivedCategoryFactors.app (((F n).mapHomologicalComplex (.up ℤ)).obj K)
  let s : Fan D := Fan.mk (DerivedCategory.Q.obj (∏ᶜ L))
    (fun n ↦ DerivedCategory.Q.map (Pi.π L n) ≫ (e n).inv)
  have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : CountableAB4Star A := CountableAB4Star.of_hasExactLimitsOfShape_nat A
  obtain ⟨hL⟩ := derivedCategory_termwiseProduct_isLimit A ℕ L
  have : PreservesLimit (Discrete.functor L) (DerivedCategory.Q (C := A)) :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) hL
  have hs : IsLimit s := Fan.IsLimit.ofIsos
    (isLimitOfHasProductOfPreservesLimit DerivedCategory.Q L) e (Iso.refl _)
    (fun n ↦ by simp [s])
  let a := hs.conePointUniqueUpToIso (productIsProduct D)
  refine ⟨a, ?_⟩
  apply Pi.hom_ext
  intro n
  have ha : a.hom ≫ Pi.π D n =
      DerivedCategory.Q.map (Pi.π L n) ≫ (e n).inv :=
    hs.conePointUniqueUpToIso_hom_comp (productIsProduct D) ⟨n⟩
  change (DerivedCategory.Q.map (Pi.lift (fun n ↦
      ((adj n).mapHomologicalComplex (.up ℤ)).unit.app K)) ≫ a.hom) ≫ Pi.π D n =
    Pi.lift (fun n ↦ (adj n).mapExactDerivedCategory.unit.app
      (DerivedCategory.Q.obj K)) ≫ Pi.π D n
  have hc : Pi.lift (fun n ↦
      ((adj n).mapHomologicalComplex (.up ℤ)).unit.app K) ≫ Pi.π L n =
      ((adj n).mapHomologicalComplex (.up ℤ)).unit.app K :=
    Pi.lift_π (f := L) _ n
  have hd : Pi.lift (fun n ↦ (adj n).mapExactDerivedCategory.unit.app
      (DerivedCategory.Q.obj K)) ≫ Pi.π D n =
      (adj n).mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) :=
    Pi.lift_π (f := D) _ n
  simp only [Category.assoc, ha, ← Functor.map_comp_assoc]
  rw [hc, hd]
  apply (cancel_mono (e n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  symm
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
  change (DerivedCategory.Q.map (((adj n).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
    (G n).mapDerivedCategoryFactors.inv.app _ ≫
    (G n).mapDerivedCategory.map ((F n).mapDerivedCategoryFactors.inv.app K)) ≫
    (G n).mapDerivedCategory.map ((F n).mapDerivedCategoryFactors.hom.app K) ≫
    (G n).mapDerivedCategoryFactors.hom.app _ = _
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

end ProductComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

attribute [local irreducible] HasDerivedCategory.standard
set_option maxHeartbeats 2000000 in
-- Unfolding the coefficient-site and derived-category wrappers needs the larger elaboration budget.
attribute [local irreducible] adjunction right coefficientSequenceEvaluation
  Functor.mapHomologicalComplex Functor.mapDerivedCategory
  Adjunction.mapHomologicalComplex in
/--
The ordinary first coinduced product of a coefficient complex localizes to the
specified derived product, compatibly with the augmentation.
Source: Stacks Tags 0941 and 079P.
(blueprint: lem-coef-sequence-product-derived-comparison).

Proof: countable products of coefficient sequence modules are exact, detected by the
product-preserving coefficient evaluations and exact pro-etale products at each level.
The general localization theorem for exact countable products makes the localized
ordinary product a product in the derived category. The exact-functor factorization
isomorphisms for evaluation and coinduction identify its factors with the specified
derived factors. Transporting the product fan along these isomorphisms gives `a`.
After projection to factor n, the localized augmentation is the original adjunction
unit followed by those factorizations. The formula for the unit of the localized
adjunction identifies it with the derived unit. Product projections detect the
augmentation equation. No resolution choices or boundedness assumptions are needed. -/
theorem complexProduct_derivedComparison
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    ∃ (a : DerivedCategory.Q.obj (complexProduct l E W K) ≅
        derivedProduct l E W (DerivedCategory.Q.obj K)),
      DerivedCategory.Q.map (complexAugmentation l E W K) ≫ a.hom =
        derivedAugmentation l E W (DerivedCategory.Q.obj K) := by
  let := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  let : ∀ n, HasDerivedCategory (normalizedDVRModules l E W n) :=
    fun n ↦ HasDerivedCategory.standard _
  have := sequence_exact_products l E W
  let h := localized_product_comparison (A := coefficientSequenceModules l E W)
    (B := fun n ↦ normalizedDVRModules l E W n)
    (coefficientSequenceEvaluation l E W) (right l E W) (adjunction l E W) K
  dsimp only [complexProduct, derivedProduct, complexAugmentation, derivedAugmentation,
    CoinducedSequence.product, CoinducedSequence.augmentation, complexEvaluation, complexRight,
    complexAdjunction, coefficientSequenceDerivedEvaluation, derivedRight, derivedAdjunction,
    coefficientSequenceHasDerived, coefficientFiniteHasDerived, scalarReductionTargetDerived] at ⊢ h
  exact h

end WeilConjectures.CoefficientCoinduction
