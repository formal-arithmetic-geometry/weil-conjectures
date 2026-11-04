/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTransComp
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

/-- The derived restriction of global sections along an endomorphism `g` of `S`: the restriction
`Γ ⟶ g^* ⋙ Γ` descended through exact localization, with the canonical L-to-exact comparison.
For `g = (h ^ r).hom` this is `derivedPointRestriction A S h r`. -/
def derivedGlobalSectionsRestriction (g : S ⟶ S) :
    (Sheaf.Γ (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor ⋙
        (Sheaf.Γ (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatTrans (globalSectionsToUpperStar (ModuleCat.{u + 1} A) g) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom ≫
    (Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).symm _).hom

/-- The derived restriction of global sections along a composite `f ≫ g` of endomorphisms of
`S` is the composite of the derived restrictions, followed by the derived pullback composition
isomorphism `leftDerivedUpperStarComp`. -/
lemma derivedGlobalSectionsRestriction_comp_app (f g : S ⟶ S)
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :
    (derivedGlobalSectionsRestriction A S (f ≫ g)).app L =
      (derivedGlobalSectionsRestriction A S g).app L ≫
        (derivedGlobalSectionsRestriction A S f).app
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj L) ≫
        (Sheaf.Γ (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).mapDerivedCategory.map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).inv.app L) := by
  have key := congr_app (Functor.mapDerivedCategoryNatTrans_comp_mapDerivedCategoryCompIso
    (upperStarComp (ModuleCat.{u + 1} A) f g)
    (globalSectionsToUpperStar (ModuleCat.{u + 1} A) g)
    (globalSectionsToUpperStar (ModuleCat.{u + 1} A) f)
    (globalSectionsToUpperStar (ModuleCat.{u + 1} A) (f ≫ g))
    (globalSectionsToUpperStar_comp (ModuleCat.{u + 1} A) f g)) L
  simp only [derivedGlobalSectionsRestriction, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, NatTrans.comp_app, Iso.trans_inv,
    Iso.symm_inv, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc] at key ⊢
  rw [← Functor.map_comp_assoc _
      ((f)^*[ModuleCat A].leftDerivedFunctorIsoMapDerivedCategory.inv.app _),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp_assoc _ (((g)^*[ModuleCat A] ⋙
      (f)^*[ModuleCat A]).leftDerivedFunctorIsoMapDerivedCategory.inv.app _),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    (Functor.mapDerivedCategoryNatTrans
      (globalSectionsToUpperStar (ModuleCat A) f)).naturality_assoc,
    ((f)^*[ModuleCat A].mapDerivedCategoryCompIso
      (Sheaf.Γ (Scheme.ProEt.topology S) (ModuleCat A))).hom.naturality_assoc,
    Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← reassoc_of% key]
  simp

/-- A version of `derivedGlobalSectionsRestriction_comp_app` for an endomorphism which is only
propositionally equal to the composite, with the compositor transported along
`leftDerivedUpperStarCongr`. -/
lemma derivedGlobalSectionsRestriction_comp_app_of_eq {f g k : S ⟶ S}
    (hk : k = f ≫ g)
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :
    (derivedGlobalSectionsRestriction A S k).app L =
      (derivedGlobalSectionsRestriction A S g).app L ≫
        (derivedGlobalSectionsRestriction A S f).app
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj L) ≫
        (Sheaf.Γ (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).mapDerivedCategory.map
          (((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).symm ≪≫
            leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) hk.symm).hom.app L) := by
  subst hk
  simpa using derivedGlobalSectionsRestriction_comp_app A S f g L

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
          ((derivedPointCompositor A S h m).hom.app L) :=
  derivedGlobalSectionsRestriction_comp_app_of_eq A S
    (congrArg Iso.hom (pow_succ h m)) L

end AlgebraicGeometry.ProEtale
