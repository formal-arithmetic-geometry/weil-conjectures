/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections

/-! # Composition of localized restriction at an automorphic point

Source: Stacks 03CE, 03D3 and 06UM; the point-insertion step of the compact-support
Frobenius power formula (blueprint: lem-trf-derived-point-restriction-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) (h : Aut S)
variable [PreservesFiniteColimits (Sheaf.Γ (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))]

/-- Restriction descended through exact localization, with the canonical L-to-exact comparison.
Source: Stacks 03CE and 06UM (blueprint: lem-trf-derived-point-restriction-composition). -/
def derivedPointRestriction (r : ℕ) :
    (Sheaf.Γ (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) (h ^ r).hom).leftDerivedFunctor ⋙
        (Sheaf.Γ (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatTrans
      (globalSectionsToUpperStar (ModuleCat.{u + 1} A) (h ^ r).hom) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom ≫
    (Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) (h ^ r).hom).symm _).hom

/-- The normalized compositor for successive powers of an automorphism.
Source: derived inverse-image composition
(blueprint: lem-trf-derived-point-restriction-composition). -/
def derivedPointCompositor (m : ℕ) :
    (upperStar (ModuleCat.{u + 1} A) (h ^ m).hom).leftDerivedFunctor ⋙
        (upperStar (ModuleCat.{u + 1} A) h.hom).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} A) (h ^ (m + 1)).hom).leftDerivedFunctor :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) h.hom (h ^ m).hom).symm ≪≫
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} A)
      (congrArg Iso.hom (pow_succ h m)).symm

/-- The localized restriction insertion respects powers with the specified compositor.
Source: restriction composition (Stacks 03CE and 06UM), exact localization and the
normalized derived pullback composition
(blueprint: lem-trf-derived-point-restriction-composition).

Proof: the underived restriction composition is `globalSectionsToUpperStar_comp`.
Apply exact localization to this identity. Naturality of the localization compositor
and its associativity identify the two localized paths. Conjugate each pullback by
its canonical L-to-exact comparison. Expanding the specified derived compositor
cancels the intermediate comparisons and gives exactly the displayed formula. -/
theorem derivedPointRestriction_composition (m : ℕ)
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :
    (derivedPointRestriction A S h (m + 1)).app L =
      (derivedPointRestriction A S h m).app L ≫
        (derivedPointRestriction A S h 1).app
          ((upperStar (ModuleCat.{u + 1} A) (h ^ m).hom).leftDerivedFunctor.obj L) ≫
        (Sheaf.Γ (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).mapDerivedCategory.map
          ((derivedPointCompositor A S h m).hom.app L) := by
  sorry

end AlgebraicGeometry.ProEtale
