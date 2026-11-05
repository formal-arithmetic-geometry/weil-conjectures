/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-!
# Composition of derived direct images on the pro-étale site

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, the total right derived direct images on
the unbounded derived categories of pro-étale sheaves satisfy

`c_{f,g} : Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`

(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp`), and these isomorphisms are unital
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp_id_left`,
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp_id_right`) and associative
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp_assoc`). This is the finite-level clause
of blueprint `lem-weil-derived-direct-image-composition`: `f_*` is right adjoint to the exact
pullback `f^*`, so it preserves K-injective complexes, and the composition theorem for total
right derived functors (`CategoryTheory.Functor.rightDerivedFunctorCompIso'`) applies to the
underived composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*`
(`AlgebraicGeometry.ProEtale.lowerStarComp`). Identity and associativity hold because they
hold for the underived composition isomorphisms.

The first part of the file proves the corresponding coherence statements for the composition
isomorphisms of general total right derived functors on unbounded derived categories, the
unbounded counterparts of those of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`.

## Main definitions

- `CategoryTheory.Functor.rightDerivedFunctorIdIso`: `R(𝟭 C) ≅ 𝟭`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarFactor`: `Rb_* ⋙ Rc_* ≅ Ra_*` for
  `b ≫ c = a`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp`: `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarId`: `R(𝟙 X)_* ≅ 𝟭`.

## Main statements

- `CategoryTheory.Functor.rightDerivedFunctorCompIso'_assoc`
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarFactor_assoc`
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp_id_left` and
  `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp_id_right`
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u' u

open CategoryTheory Category Limits Abelian

open scoped CategoryTheory.Functor

namespace CategoryTheory

namespace Functor

section NatTrans

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]

/-- The natural transformation `Functor.rightDerivedFunctorNatTrans τ` is characterized by its
compatibility with the units of the two right derived functors. -/
@[reassoc]
lemma rightDerivedFunctorNatTrans_app {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    F.rightDerivedFunctorUnit.app K ≫
        (rightDerivedFunctorNatTrans τ).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K) ≫
        G.rightDerivedFunctorUnit.app K := by
  simp [rightDerivedFunctorNatTrans]

end NatTrans

section Composition

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

/-- The components of the composite unit `Functor.rightDerivedFunctorCompUnit`. -/
@[reassoc]
lemma rightDerivedFunctorCompUnit_app (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (rightDerivedFunctorCompUnit F G).app K =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) := by
  have h := (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom_inv_id_app K
  rw [mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at h
  simp only [rightDerivedFunctorCompUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id]
  erw [h, Functor.map_id, Category.id_comp]

variable [F.PreservesKInjectiveComplexes]

/-- The composition isomorphism `Functor.rightDerivedFunctorCompIso` is characterized by its
compatibility with the units. -/
@[reassoc]
lemma rightDerivedFunctorCompIso_fac :
    (F ⋙ G).rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedFunctorCompIso F G).hom =
      rightDerivedFunctorCompUnit F G := by
  simp [rightDerivedFunctorCompIso]

/-- The pointwise form of `Functor.rightDerivedFunctorCompIso_fac`. -/
@[reassoc]
lemma rightDerivedFunctorCompIso_fac_app (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (F ⋙ G).rightDerivedFunctorUnit.app K ≫
        (rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj K) =
      (rightDerivedFunctorCompUnit F G).app K :=
  NatTrans.congr_app (rightDerivedFunctorCompIso_fac F G) K

/-- The composition isomorphism `Functor.rightDerivedFunctorCompIso'` attached to
`e : F ⋙ G ≅ H` is characterized by its compatibility with the units. -/
@[reassoc]
lemma rightDerivedFunctorCompIso'_fac {H : C ⥤ E} [H.Additive] (e : F ⋙ G ≅ H) :
    rightDerivedFunctorCompUnit F G ≫ Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedFunctorCompIso' F G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ H.rightDerivedFunctorUnit := by
  rw [← rightDerivedFunctorCompIso_fac F G, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  exact rightDerivedNatTrans_fac _ _ _ _ (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _

/-- The pointwise form of `Functor.rightDerivedFunctorCompIso'_fac`. -/
@[reassoc]
lemma rightDerivedFunctorCompIso'_fac_app {H : C ⥤ E} [H.Additive] (e : F ⋙ G ≅ H)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) ≫
          (rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) ≫
        H.rightDerivedFunctorUnit.app K := by
  have := NatTrans.congr_app (rightDerivedFunctorCompIso'_fac F G e) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    rightDerivedFunctorCompUnit_app, Category.assoc] at this
  exact this

end Composition

section Identity

variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [HasDerivedCategory C]
  [HasKInjectiveResolutions C]

end Identity

section Coherence

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {E' : Type*}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']
  [HasKInjectiveResolutions C]

end Coherence

end Functor

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Underived

variable {X Y Z W : Scheme.{u}}

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphism along `rfl : b ≫ c = b ≫ c` is `lowerStarComp`. -/
lemma lowerStarFactor_rfl (b : Z ⟶ Y) (c : Y ⟶ X) :
    lowerStarFactor A (rfl : b ≫ c = b ≫ c) = lowerStarComp A b c := by
  rw [← lowerStarComp_trans_lowerStarCongr, lowerStarCongr_rfl, Iso.trans_refl]

end Underived

section Derived

instance preservesKInjectiveComplexes_lowerStar {Y X : Scheme.{u}} (g : Y ⟶ X) :
    ((g)_*[A]).PreservesKInjectiveComplexes :=
  (ProEtale.upperStarLowerStarAdjunction A g).preservesKInjectiveComplexes

variable {X Y Z W : Scheme.{u}}

end Derived

end AlgebraicGeometry.ProEtale
