/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCanonicalComparisons


/-! # The canonical first-product comparison preserves augmentation

Source: Stacks 015F and 0941.
(blueprint: lem-coef-sequence-canonical-augmentation).
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
-- Check localization proofs sequentially to bound memory from large coefficient functors.
set_option Elab.async false
universe uC uD vC vD wC wD

private theorem exact_unit
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
    (X : CochainComplex C ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj X) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (a.mapHomologicalComplex (.up ℤ)).localization_unit_app
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory X

private theorem product_unit_comparison
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {D : ℕ → Type uD} [∀ n, Category.{vD} (D n)] [∀ n, Abelian (D n)]
    [∀ n, HasDerivedCategory.{wD} (D n)]
    (F : ∀ n, C ⥤ D n) (G : ∀ n, D n ⥤ C)
    [∀ n, (F n).Additive] [∀ n, (G n).Additive]
    [∀ n, PreservesFiniteLimits (F n)] [∀ n, PreservesFiniteColimits (F n)]
    [∀ n, PreservesFiniteLimits (G n)] [∀ n, PreservesFiniteColimits (G n)]
    (a : ∀ n, F n ⊣ G n)
    [HasCountableProducts (CochainComplex C ℤ)]
    [HasCountableProducts (DerivedCategory C)] (K : CochainComplex C ℤ) :
    DerivedCategory.Q.map
        (Pi.lift fun n ↦ ((a n).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      (Pi.lift fun n ↦ DerivedCategory.Q.map
        (Pi.π (fun n ↦ ((G n).mapHomologicalComplex (.up ℤ)).obj
          (((F n).mapHomologicalComplex (.up ℤ)).obj K)) n) ≫
        (G n).mapDerivedCategoryFactors.inv.app
          (((F n).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (G n).mapDerivedCategory.map ((F n).mapDerivedCategoryFactors.inv.app K)) =
      Pi.lift (fun n ↦ (a n).mapExactDerivedCategory.unit.app
        (DerivedCategory.Q.obj K)) := by
  have hc := Pi.lift_π
    (fun n ↦ ((a n).mapHomologicalComplex (.up ℤ)).unit.app K)
  apply Pi.hom_ext
  intro n
  dsimp only [Functor.comp_obj] at hc ⊢
  simp only [Category.assoc, Pi.lift_π]
  rw [← DerivedCategory.Q.map_comp_assoc, hc n]
  exact (exact_unit (a n) K).symm

-- Keep the localization implementation abstract while checking coefficient identities.
attribute [local irreducible] Adjunction.mapHomologicalComplex Adjunction.homEquiv
attribute [local irreducible] Adjunction.localization
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
attribute [local irreducible] HasDerivedCategory.standard

universe u
open AlgebraicGeometry
namespace WeilConjectures.CoefficientCoinduction
attribute [local irreducible] adjunction right coefficientSequenceEvaluation
  CategoryTheory.constantSheaf normalizedDVRQuotient coefficientSequenceCommRingSheaf
attribute [local implicit_reducible] CoinducedSequence.product CoinducedSequence.relations
attribute [local implicit_reducible] coefficientSequenceHasDerived coefficientFiniteHasDerived
  scalarReductionTargetDerived derivedRight derivedAdjunction


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})


section
attribute [local irreducible] Functor.mapHomologicalComplex

set_option maxHeartbeats 2000000 in
-- The explicit coefficient-site functors require additional elaboration heartbeats.
/-- The canonical first-product comparison preserves augmentation.
Proof: by the product universal property it suffices to compare the projections to
each level n. The n-th projection of the left side is Q of the ordinary adjunction
unit at K followed by the inverse exact-functor comparisons for coinduction and
evaluation, which are the factors of the canonical comparison. By the localized unit
formula for the exact evaluation/coinduction adjunction (`localization_unit_app`),
this composite is the unit of the localized adjunction at Q K, i.e. the n-th
projection of the derived augmentation (`product_unit_comparison` above, specialized
to the coefficient evaluations, coinductions and their adjunctions).
Source: Stacks Tag 015F, localization of exact adjunction units.
(blueprint: lem-coef-sequence-canonical-augmentation).
-/
theorem canonicalAugmentationComparison
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    DerivedCategory.Q.map (complexAugmentation l E W K) ≫
      canonicalProductComparison l E W K =
      derivedAugmentation l E W (DerivedCategory.Q.obj K) := by
  let := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  let : ∀ n, HasDerivedCategory (normalizedDVRModules l E W n) :=
    fun n ↦ HasDerivedCategory.standard _
  have h := product_unit_comparison (C := coefficientSequenceModules l E W)
    (D := fun n ↦ normalizedDVRModules l E W n)
    (coefficientSequenceEvaluation l E W) (right l E W) (adjunction l E W) K
  dsimp only [canonicalProductComparison, canonicalProductFactorComparison,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv,
    complexProduct, derivedProduct, complexAugmentation, derivedAugmentation,
    CoinducedSequence.product, CoinducedSequence.augmentation, complexEvaluation, complexRight,
    complexAdjunction, coefficientSequenceDerivedEvaluation, derivedRight, derivedAdjunction,
    coefficientSequenceHasDerived, coefficientFiniteHasDerived, scalarReductionTargetDerived] at ⊢ h
  exact h

end

end WeilConjectures.CoefficientCoinduction
