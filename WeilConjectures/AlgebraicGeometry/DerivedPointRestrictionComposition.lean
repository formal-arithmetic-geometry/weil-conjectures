/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCompIsoNatTrans
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

/-- Restriction of global sections along a composite `g₁ ≫ g₂ = g`, descended through exact
localization and conjugated by the canonical L-to-exact comparisons, is the composite of the
descended restrictions followed by the derived pullback compositor. -/
lemma mapDerivedCategoryNatTrans_globalSectionsToUpperStar_comp {X Y Z : Scheme.{u}}
    (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) (g : X ⟶ Z) (w : g₁ ≫ g₂ = g)
    [PreservesFiniteColimits (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))]
    [PreservesFiniteColimits (Sheaf.Γ (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))]
    [PreservesFiniteColimits (Sheaf.Γ (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))]
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) :
    (Functor.mapDerivedCategoryNatTrans
        (globalSectionsToUpperStar (ModuleCat.{u + 1} A) g)).app L ≫
        (Functor.mapDerivedCategoryCompIso _ _).hom.app L ≫
        (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv.app L) =
      (Functor.mapDerivedCategoryNatTrans
        (globalSectionsToUpperStar (ModuleCat.{u + 1} A) g₂)).app L ≫
        (Functor.mapDerivedCategoryCompIso _ _).hom.app L ≫
        (Sheaf.Γ (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g₂).inv.app L) ≫
        (Functor.mapDerivedCategoryNatTrans
          (globalSectionsToUpperStar (ModuleCat.{u + 1} A) g₁)).app
            ((upperStar (ModuleCat.{u + 1} A) g₂).leftDerivedFunctor.obj L) ≫
        (Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((upperStar (ModuleCat.{u + 1} A) g₂).leftDerivedFunctor.obj L) ≫
        (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g₁).inv.app
            ((upperStar (ModuleCat.{u + 1} A) g₂).leftDerivedFunctor.obj L)) ≫
        (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).mapDerivedCategory.map
          (((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂).symm ≪≫
            leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) w).hom.app L) := by
  subst w
  have key := Functor.mapDerivedCategoryNatTrans_comp_compIso_hom_app_eq
    (globalSectionsToUpperStar (ModuleCat.{u + 1} A) (g₁ ≫ g₂))
    (globalSectionsToUpperStar (ModuleCat.{u + 1} A) g₂)
    (globalSectionsToUpperStar (ModuleCat.{u + 1} A) g₁)
    (upperStarComp (ModuleCat.{u + 1} A) g₁ g₂)
    (globalSectionsToUpperStar_comp (ModuleCat.{u + 1} A) g₁ g₂) L
  have hn := (Functor.mapDerivedCategoryNatTrans
      (globalSectionsToUpperStar (ModuleCat.{u + 1} A) g₁) ≫
    (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} A) g₁)
      (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).hom).naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g₂).hom.app L)
  simp only [NatTrans.comp_app, Functor.comp_map] at hn
  simp only [leftDerivedUpperStarCongr_rfl, Iso.trans_refl, Iso.symm_hom,
    leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  simp only [Category.assoc, leftDerivedUpperStarIsoMapDerivedCategory] at hn
  simp only [← Iso.app_inv, ← Iso.app_hom, Iso.map_inv_hom_id_assoc]
  simp only [Iso.app_inv, Iso.app_hom]
  rw [← reassoc_of% hn]
  simp only [← Iso.app_inv, ← Iso.app_hom, Iso.map_inv_hom_id_assoc]
  simp only [Iso.app_inv, Iso.app_hom]
  rw [← reassoc_of% key]
  simp only [← Iso.app_inv, ← Iso.app_hom, Iso.map_hom_inv_id_assoc]

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
  simp only [derivedPointRestriction, derivedPointCompositor, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom, Category.assoc]
  exact mapDerivedCategoryNatTrans_globalSectionsToUpperStar_comp A h.hom (h ^ m).hom _
    (congrArg Iso.hom (pow_succ h m)).symm L

end AlgebraicGeometry.ProEtale
