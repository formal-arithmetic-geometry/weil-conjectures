/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.ExceptionalSiteRealization
/-! # Derived realization of the actual etale/pro-etale system comparison
Source: blueprint def-weil-exceptional-inverse-image. All ordinary maps are fixed on
sections or by adjunction transposes; their derived maps retain the localization units.
(blueprint: def-pur-adic-derived-site-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  (P : StrictEtaleEvaluation W (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E))
  (B : IntegralExceptionalComparison l E W P)

/-- The complete inverse realization normalization on all cochain complexes.
Source: blueprint integral exceptional image
(blueprint: def-pur-adic-derived-site-realization). -/
def IsIntegralExceptionalSiteDerivedInverse (n : ℕ)
    (e : (B.derived.level n).inverse ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory) :
            Prop :=
      ∀ J : CochainComplex (strictEtaleLevel W (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) ℤ,
        e.hom.app (DerivedCategory.Q.obj J) ≫
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory.map
              ((integralExceptionalEtaleRealization l E W n).mapDerivedCategoryFactors.hom.app
                 J) ≫
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
              W).mapDerivedCategoryFactors.hom.app
                (((integralExceptionalEtaleRealization l E W n).mapHomologicalComplex
                   (.up ℤ)).obj J) =
        (integralExceptionalProRealization l E W n).mapDerivedCategory.map
          ((B.derived.level n).inverseFactors.hom.app J) ≫
        (integralExceptionalProRealization l E W n).mapDerivedCategoryFactors.hom.app
          ((((B.ordinary.lift n).modules).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (integralExceptionalSiteInverse l E W P B n).hom (.up ℤ)).app J)

/-- The exact derived site inverse comparison, fixed on every cochain representative.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization).
Proof: apply exact localization to the preceding ordinary inverse comparison and
compose the two specified factorization isomorphisms. Their square is the displayed
condition. Every derived arrow is represented by a roof, proving uniqueness. -/
theorem integralExceptionalSiteDerivedInverse_existsUnique (n : ℕ) :
    ∃! e : (B.derived.level n).inverse ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory,
      IsIntegralExceptionalSiteDerivedInverse l E W P B n e := by
  sorry

/-- The exact inverse comparison, fixed by its universal representative square.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization). -/
@[no_expose] def integralExceptionalSiteDerivedInverse (n : ℕ) :
    (B.derived.level n).inverse ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory :=
  (integralExceptionalSiteDerivedInverse_existsUnique l E W P B n).choose

/-- The actual cochain-level unit of derived site direct image.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization). -/
def integralExceptionalSiteFixedRightUnit (n : ℕ)
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
    DerivedCategory.Q.obj
      (((ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapHomologicalComplex
           (.up ℤ)).obj J) ⟶
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor.obj
         (DerivedCategory.Q.obj J) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctorUnit.app
         ((HomotopyCategory.quotient _ _).obj J) ≫
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor.map
         ((DerivedCategory.quotientCompQhIso _).inv.app J)

/-- The complete right realization normalization on all cochain complexes.
Source: blueprint integral exceptional image
(blueprint: def-pur-adic-derived-site-realization). -/
def IsIntegralExceptionalSiteDerivedRight (n : ℕ)
    (e : (B.derived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor) :
            Prop :=
      ∀ J : CochainComplex (coefficientLevelModules (J := Scheme.ProEt.topology W)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n) ℤ,
        (integralExceptionalEtaleRealization l E W n).mapDerivedCategory.map
          ((B.derived.level n).directUnit.app J) ≫ e.hom.app (DerivedCategory.Q.obj J) ≫
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor.map
          ((integralExceptionalProRealization l E W n).mapDerivedCategoryFactors.hom.app J) =
        (integralExceptionalEtaleRealization l E W n).mapDerivedCategoryFactors.hom.app
          (((B.ordinary.right n).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (integralExceptionalSiteRight l E W P B n).hom (.up ℤ)).app J) ≫
        integralExceptionalSiteFixedRightUnit l E W n
          (((integralExceptionalProRealization l E W n).mapHomologicalComplex
             (.up ℤ)).obj J)

/-- The derived site direct comparison is fixed by both universal right-derived units.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization).
Proof: on K-injective representatives both derived units are invertible and the
ordinary section comparison determines the map. Exact realization is an equivalence,
so it preserves K-injective representatives. Universal right derivation extends this
map uniquely and gives the displayed square on all complexes. -/
theorem integralExceptionalSiteDerivedRight_existsUnique (n : ℕ) :
    ∃! e : (B.derived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor,
      IsIntegralExceptionalSiteDerivedRight l E W P B n e := by
  sorry

/-- The universal-unit-normalized derived site direct comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization). -/
@[no_expose] def integralExceptionalSiteDerivedRight (n : ℕ) :
    (B.derived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor :=
  (integralExceptionalSiteDerivedRight_existsUnique l E W P B n).choose
end WeilConjectures
