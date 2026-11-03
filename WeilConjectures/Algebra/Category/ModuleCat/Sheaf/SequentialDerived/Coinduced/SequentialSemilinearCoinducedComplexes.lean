/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearCoinducedProducts
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # The coinduced short complex and its canonical localization maps

Source: Stacks 0941, 0152 and 015F, the locally finite two-term resolution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived.Coinduced

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

abbrev complexEvaluation (n : ℕ) := (systemEvaluation B n).mapHomologicalComplex (.up ℤ)
abbrev complexRight (n : ℕ) :=
  (SequenceCoinduced.rightExtension B n).mapHomologicalComplex (.up ℤ)
abbrev complexRestriction (n : ℕ) :=
  (systemRestriction B (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)
abbrev complexAdjunction (n : ℕ) :=
  (SequenceCoinduced.adjunction B n).mapHomologicalComplex (.up ℤ)
abbrev complexTransition (n : ℕ) :=
  (strictSystemTransition B (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)

abbrev complexProductFunctor :=
  CoinducedSequence.productFunctor (complexEvaluation B) (complexRight B)
abbrev complexRelationsFunctor :=
  CoinducedSequence.relationsFunctor (complexEvaluation B) (complexRight B)
    (complexRestriction B)
abbrev complexAugmentationNat :=
  CoinducedSequence.augmentationNat (complexEvaluation B) (complexRight B)
    (complexAdjunction B)
abbrev complexDifferenceNat :=
  CoinducedSequence.differenceNat (complexEvaluation B) (complexRight B)
    (complexAdjunction B) (complexRestriction B) (complexTransition B)

/-- The ordinary two-term coinduced resolution as a short complex of complexes.
Source: Stacks 0941
(blueprint: def-sf-sequential-semilinear-coinduced-complexes). -/
def complexSequence (K : CochainComplex (StrictRingSystem B) ℤ) :
    ShortComplex (CochainComplex (StrictRingSystem B) ℤ) :=
  ShortComplex.mk ((complexAugmentationNat B).app K) ((complexDifferenceNat B).app K)
    (CoinducedSequence.augmentation_defect (complexEvaluation B) (complexRight B)
      (complexAdjunction B) (complexRestriction B) (complexTransition B) K)

/-- A chain map gives the specified morphism between the two short complexes.
Source: Stacks 0941
(blueprint: def-sf-sequential-semilinear-coinduced-complexes). -/
def complexSequenceMap {K L : CochainComplex (StrictRingSystem B) ℤ} (f : K ⟶ L) :
    complexSequence B K ⟶ complexSequence B L where
  τ₁ := f
  τ₂ := (complexProductFunctor B).map f
  τ₃ := (complexRelationsFunctor B).map f
  comm₁₂ := (complexAugmentationNat B).naturality f
  comm₂₃ := (complexDifferenceNat B).naturality f

/-- Exact-functor localization identifies each ordinary coinduced factor.
Source: Stacks 015F
(blueprint: def-sf-sequential-semilinear-coinduced-complexes). -/
def productFactorComparison (n : ℕ) :
    complexEvaluation B n ⋙ complexRight B n ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ derivedSystemEvaluation B n ⋙ derivedRight B n :=
  Functor.isoWhiskerLeft (complexEvaluation B n)
      (SequenceCoinduced.rightExtension B n).mapDerivedCategoryFactors.symm ≪≫
    Functor.isoWhiskerRight (systemEvaluation B n).mapDerivedCategoryFactors.symm
      (derivedRight B n)

/-- Exact-functor localization identifies each scalar-restricted relation factor.
Source: Stacks 015F
(blueprint: def-sf-sequential-semilinear-coinduced-complexes). -/
def relationsFactorComparison (n : ℕ) :
    complexEvaluation B n ⋙ complexRestriction B n ⋙ complexRight B (n + 1) ⋙
        DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ derivedSystemEvaluation B n ⋙ Helper.adjacentRestriction B n ⋙
        derivedRight B (n + 1) :=
  Functor.isoWhiskerLeft (complexEvaluation B n ⋙ complexRestriction B n)
      (SequenceCoinduced.rightExtension B (n + 1)).mapDerivedCategoryFactors.symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (complexEvaluation B n)
        (systemRestriction B (Nat.le_succ n)).mapDerivedCategoryFactors.symm)
      (derivedRight B (n + 1)) ≪≫
    Functor.isoWhiskerRight (systemEvaluation B n).mapDerivedCategoryFactors.symm
      (Helper.adjacentRestriction B n ⋙ derivedRight B (n + 1))

/-- The canonical component of the first product comparison.
Source: Stacks 015F
(blueprint: def-sf-sequential-semilinear-coinduced-complexes). -/
def productComparisonComponent (n : ℕ) :
    complexProductFunctor B ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedSystemEvaluation B n ⋙ derivedRight B n :=
  Functor.whiskerRight (CoinducedSequence.productProjection
      (complexEvaluation B) (complexRight B) n) DerivedCategory.Q ≫
    (productFactorComparison B n).hom

/-- The canonical component of the relation product comparison.
Source: Stacks 015F
(blueprint: def-sf-sequential-semilinear-coinduced-complexes). -/
def relationsComparisonComponent (n : ℕ) :
    complexRelationsFunctor B ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedSystemEvaluation B n ⋙ Helper.adjacentRestriction B n ⋙
        derivedRight B (n + 1) :=
  Functor.whiskerRight (CoinducedSequence.relationsProjection
      (complexEvaluation B) (complexRight B) (complexRestriction B) n) DerivedCategory.Q ≫
    (relationsFactorComparison B n).hom

/-- The canonical comparison is the product lift of the localized projections.
Source: Stacks 015F and 079P
(blueprint: def-sf-sequential-semilinear-coinduced-complexes). -/
def productComparison : complexProductFunctor B ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ productFunctor B where
  app K := Pi.lift (fun n ↦ (productComparisonComponent B n).app K)
  naturality {K L} f := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_π, Functor.comp_map, productFunctor,
      CoinducedSequence.productFunctor, Pi.map_π]
    rw [← Category.assoc, Pi.lift_π]
    exact (productComparisonComponent B n).naturality f

/-- The canonical comparison for the relation product.
Source: Stacks 015F and 079P
(blueprint: def-sf-sequential-semilinear-coinduced-complexes). -/
def relationsComparison : complexRelationsFunctor B ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ relationsFunctor B where
  app K := Pi.lift (fun n ↦ (relationsComparisonComponent B n).app K)
  naturality {K L} f := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_π, Functor.comp_map, relationsFunctor,
      CoinducedSequence.relationsFunctor, Pi.map_π]
    rw [← Category.assoc, Pi.lift_π]
    exact (relationsComparisonComponent B n).naturality f

end SheafOfModules.SequentialDerived.Coinduced
