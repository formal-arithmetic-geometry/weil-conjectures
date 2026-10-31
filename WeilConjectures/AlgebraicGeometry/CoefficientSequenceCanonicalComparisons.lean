/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinducedComplexes

/-! # Canonical maps comparing the coinduced products with their derived products

Source: Stacks Tags 015F, 079P and 0941.
(blueprint: def-coef-sequence-canonical-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.CoefficientCoinduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

/-- The ordinary and derived first-product factors agree by exact-functor localization.
Source: Stacks 015F (blueprint: def-coef-sequence-canonical-comparisons). -/
def canonicalProductFactorComparison
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    DerivedCategory.Q.obj
        ((complexRight l E W n).obj ((complexEvaluation l E W n).obj K)) ≅
      (derivedRight l E W n).obj
        ((coefficientSequenceDerivedEvaluation l E W n).obj (DerivedCategory.Q.obj K)) :=
  ((right l E W n).mapDerivedCategoryFactors.app _).symm ≪≫
    (derivedRight l E W n).mapIso
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app K).symm

/-- The adjacent relation factor is identified using the three exact-functor comparisons.
Source: Stacks 015F (blueprint: def-coef-sequence-canonical-comparisons). -/
def canonicalRelationsFactorComparison
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    DerivedCategory.Q.obj
        ((complexRight l E W (n + 1)).obj
          ((complexRestriction l E W n).obj ((complexEvaluation l E W n).obj K))) ≅
      (derivedRight l E W (n + 1)).obj
        ((normalizedDVRRes l E W (Nat.le_succ n)).obj
          ((coefficientSequenceDerivedEvaluation l E W n).obj (DerivedCategory.Q.obj K))) :=
  ((right l E W (n + 1)).mapDerivedCategoryFactors.app _).symm ≪≫
    (derivedRight l E W (n + 1)).mapIso
      (((normalizedDVRModuleRes l E W (Nat.le_succ n)).mapDerivedCategoryFactors.app
          ((complexEvaluation l E W n).obj K)).symm ≪≫
        (normalizedDVRRes l E W (Nat.le_succ n)).mapIso
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app K).symm)

/-- The canonical first-product map is the lift of the localized projections.
Source: Stacks 079P and 0941 (blueprint: def-coef-sequence-canonical-comparisons). -/
def canonicalProductComparison
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    DerivedCategory.Q.obj (complexProduct l E W K) ⟶
      derivedProduct l E W (DerivedCategory.Q.obj K) :=
  Pi.lift fun n ↦ DerivedCategory.Q.map
    (Pi.π (fun n ↦ (complexRight l E W n).obj ((complexEvaluation l E W n).obj K)) n) ≫
      (canonicalProductFactorComparison l E W K n).hom

/-- The canonical relation-product map is the lift of the localized relation projections.
Source: Stacks 079P and 0941 (blueprint: def-coef-sequence-canonical-comparisons). -/
def canonicalRelationsComparison
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    DerivedCategory.Q.obj (complexRelations l E W K) ⟶
      derivedRelations l E W (DerivedCategory.Q.obj K) :=
  Pi.lift fun n ↦ DerivedCategory.Q.map
    (Pi.π (fun n ↦ (complexRight l E W (n + 1)).obj
      ((complexRestriction l E W n).obj ((complexEvaluation l E W n).obj K))) n) ≫
      (canonicalRelationsFactorComparison l E W K n).hom

end WeilConjectures.CoefficientCoinduction
