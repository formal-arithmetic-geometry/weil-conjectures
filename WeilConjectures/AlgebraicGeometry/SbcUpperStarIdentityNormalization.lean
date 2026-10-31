/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RootTowerCoordinateFace
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # Identity normalization for the derived upper-star compositor

Source: `literature/blueprint/latest/blueprint/sec-smooth-base-change/
sk-lem-sbc-exchange-compatibility/det-sbc-exchange-formal.proof.md`, paragraph (2).

The normalized derived upper-star composition comparison has the left and right
unit laws.  The composition comparison is `RootCoordinateFace.upperComp`, and
the identity comparison is the derived image of `CondensedRing.upperStarId`
followed by `Functor.mapDerivedCategoryIdIso`.
(blueprint: lem-sbc-upperstar-identity-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor

private theorem derived_outer_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F H : C ⥤ D) (U : D ⥤ D) [F.Additive] [H.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : U ≅ 𝟭 D) (d : H ≅ F) (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryNatIso
        (d ≪≫ F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F e.symm) ≪≫
      Functor.mapDerivedCategoryCompIso F U).hom.app K ≫
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
        (F.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategoryNatIso d).hom.app K := by
  have hi : Functor.mapDerivedCategoryNatIso F.rightUnitor = Iso.refl _ := by
    apply Iso.ext
    exact Functor.mapDerivedCategoryNatIso_refl
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hu
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Functor.whiskerLeft_app, Iso.refl_inv, NatTrans.id_app, Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_isoWhiskerLeft,
    Functor.mapDerivedCategoryNatIso_symm, hi, hu]
  erw [Category.comp_id, Category.comp_id]

private theorem derived_inner_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F H : C ⥤ D) (U : C ⥤ C) [F.Additive] [H.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : U ≅ 𝟭 C) (d : H ≅ F) (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryNatIso
        (d ≪≫ F.leftUnitor.symm ≪≫ Functor.isoWhiskerRight e.symm F) ≪≫
      Functor.mapDerivedCategoryCompIso U F).hom.app K ≫
      F.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app K) =
      (Functor.mapDerivedCategoryNatIso d).hom.app K := by
  have hi : Functor.mapDerivedCategoryNatIso F.leftUnitor = Iso.refl _ := by
    apply Iso.ext
    exact Functor.mapDerivedCategoryNatIso_refl
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hu
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Functor.whiskerRight_app, Iso.refl_inv, NatTrans.id_app, Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_isoWhiskerRight,
    Functor.mapDerivedCategoryNatIso_symm, hi, hu, ← Functor.map_comp]
  erw [Category.comp_id, Category.comp_id]

private theorem derived_upper_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (K : DerivedCategory (RootCoordinateFace.Modules Λ Y)) :
    (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarCongr Λ h)).hom.app K =
      eqToHom (congrArg (fun a ↦ (RootCoordinateFace.upper Λ a).obj K) h) := by
  cases h
  rw [CondensedRing.upperStarCongr_self, Functor.mapDerivedCategoryNatIso_refl]
  rfl

namespace AlgebraicGeometry.Scheme

/-- The normalized derived upper-star composition comparison satisfies both unit laws.

Source: `literature/blueprint/latest/blueprint/sec-smooth-base-change/
sk-lem-sbc-exchange-compatibility/det-sbc-exchange-formal.proof.md`, paragraph (2).
Proof.
1. Unfold the comparisons: `RootCoordinateFace.upperComp Λ a b` is the derived image
   `Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ a b)` followed by the
   exact-derived composition comparison `μ = Functor.mapDerivedCategoryCompIso`
   (lem-sfb-exact-derived-composition), and `I_T` is the derived image of
   `CondensedRing.upperStarId Λ T` followed by `Functor.mapDerivedCategoryIdIso`.
2. The underived comparisons obey both unit laws
   (lem-sbc-module-upperstar-underived-unit-laws: `upperStarComp_id_left`,
   `upperStarComp_id_right`).  By exact-derived pasting
   (lem-sp-exact-derived-transformation-pasting) `mapDerivedCategoryNatIso` is compatible
   with vertical composition, with whiskering through `μ`, and sends `eqToIso` to `eqToIso`.
   For the left law, substitute the underived law into `C_{𝟙 X,f}.hom`; the whiskered factor
   `D(f^* ◁ (upperStarId Λ X)⁻¹)`, then `μ`, then `U_f ◁ I_X.hom` cancels to `μ_{f^*,𝟭}`
   followed by `U_f ◁ (D(𝟭) ≅ 𝟭)`, which is the identity by
   `mapDerivedCategoryCompIso_comp_id`; what remains is the derived image of
   `upperStarCongr (id_comp f) ≪≫ ρ⁻¹`, an `eqToHom`.  The right law is the same computation
   with the left unitor, whiskering on the right and `mapDerivedCategoryCompIso_id_comp`.
   Evaluating at `K` gives both equations.
(blueprint: lem-sbc-upperstar-identity-normalization)
-/
theorem sbcUpperStarIdentityNormalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (RootCoordinateFace.Modules Λ Y)) :
    ((RootCoordinateFace.upperComp Λ (𝟙 X) f).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ X) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app
          ((RootCoordinateFace.upper Λ f).obj K) =
      eqToHom (by rw [Category.id_comp]; rfl)) ∧
      ((RootCoordinateFace.upperComp Λ f (𝟙 Y)).hom.app K ≫
        (RootCoordinateFace.upper Λ f).map
          ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ Y) ≪≫
            Functor.mapDerivedCategoryIdIso _).hom.app K) =
        eqToHom (by rw [Category.comp_id]; rfl)) := by
  constructor
  · rw [RootCoordinateFace.upperComp,
      AlgebraicGeometry.ProEtale.CondensedRing.upperStarComp_id_left]
    exact (derived_outer_unit _ _ _ _ _ K).trans (derived_upper_congr Λ _ K)
  · rw [RootCoordinateFace.upperComp,
      AlgebraicGeometry.ProEtale.CondensedRing.upperStarComp_id_right]
    exact (derived_inner_unit _ _ _ _ _ K).trans (derived_upper_congr Λ _ K)

end AlgebraicGeometry.Scheme
