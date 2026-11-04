/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerEtaleConstant
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor

/-! # Naturality of the étale Kummer class under pullback

Source: blueprint lem-pur-relative-kummer-exchange-from-conclusions (auxiliary lemmas).
-/

@[expose] public section
set_option autoImplicit false
universe u' u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

section KummerNaturality

variable (P : PurityFiniteSetting.{u})

/-- The scalar-forgetting comparison of pullbacks is natural. -/
@[reassoc]
lemma upperStarForget₂Comparison_naturality' {X T : Scheme.{u}} (f : X ⟶ T)
    {B B' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)} (φ : B ⟶ B') :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).map ((P.forgetEtale T).map φ) ≫
        Etale.upperStarForget₂Comparison P.Coefficient f B' =
      Etale.upperStarForget₂Comparison P.Coefficient f B ≫
        (P.forgetEtale X).map ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).map φ) := by
  apply ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp]
  have h1 := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.naturality
    ((P.forgetEtale T).map φ)
  simp only [Functor.id_map, Functor.comp_map] at h1
  have hB := Etale.unit_comp_lowerStar_map_upperStarForget₂Comparison P.Coefficient f B
  have hB' := Etale.unit_comp_lowerStar_map_upperStarForget₂Comparison P.Coefficient f B'
  have h2 := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
    f).unit.naturality φ
  simp only [Functor.id_map, Functor.comp_map] at h2
  erw [← Category.assoc, ← h1, Category.assoc, hB', ← Category.assoc, hB]
  exact (congrArg (P.forgetEtale T).map h2).trans (Functor.map_comp _ _ _)

/-- Scalar forgetting commutes with pullback. -/
noncomputable def forgetUpperStarIso {X T : Scheme.{u}} (f : X ⟶ T) :
    P.forgetEtale T ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f ≅
      Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f ⋙ P.forgetEtale X :=
  NatIso.ofComponents (fun B ↦ asIso (Etale.upperStarForget₂Comparison P.Coefficient f B))
    (fun φ ↦ upperStarForget₂Comparison_naturality' P f φ)

/-- The degree-zero generator `ℤ ⟶ A` is compatible with pullback. -/
lemma integerToConstant_upperStar {X T : Scheme.{u}} (f : X ⟶ T) :
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app
        (AddCommGrpCat.of (ULift ℤ)) ≫ P.integerToConstant X =
      (Etale.upperStar AddCommGrpCat.{u + 1} f).map (P.integerToConstant T) ≫
        Etale.upperStarForget₂Comparison P.Coefficient f (P.constantEtale T) ≫
        (P.forgetEtale X).map ((Scheme.upperStarConstantSheafIso
          (ModuleCat.{u + 1} P.Coefficient) f).hom.app
            (ModuleCat.of P.Coefficient P.Coefficient)) := by
  have hn := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.naturality
    ((AddCommGrpCat.uliftZMultiplesAddEquiv (AddCommGrpCat.of P.Coefficient)).symm 1)
  simp only [integerToConstant, Functor.map_comp, Category.assoc, Functor.comp_map] at hn ⊢
  erw [upperStar_constantCommuteCompose_inv P f (ModuleCat.of P.Coefficient P.Coefficient),
    reassoc_of% hn]

/-- Composition of the maps induced on cohomology. -/
lemma sheafH_map_map {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    {F G H : Sheaf J AddCommGrpCat.{u + 1}} (a : F ⟶ G) (b : G ⟶ H) (n : ℕ)
    (x : Sheaf.H F n) :
    Sheaf.H.map b n (Sheaf.H.map a n x) = Sheaf.H.map (a ≫ b) n x := by
  rw [Sheaf.H.map_apply, Sheaf.H.map_apply, Sheaf.H.map_apply,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

variable (h : P.ramificationIndex ∣ P.level)

/-- The defining property of the étale Kummer class. -/
lemma moduleClassToAbelian_kummerEtale (T : Scheme.{u}) (hT : IsUnit (P.exponent : Γ(T, ⊤)))
    (s : Γ(T, ⊤)ˣ) :
    P.moduleClassToAbelian T (P.twistEtale h T) (P.kummerEtale h T hT s) =
      Sheaf.H.map (P.rootCoefficientMap h T) 1 (T.kummerδ₀ P.exponent hT (Additive.ofMul s)) :=
  (Equiv.ofBijective _ (P.moduleClassToAbelian_bijective T (P.twistEtale h T))).apply_symm_apply _

/-- The pulled-back root coefficient map. -/
lemma rootCoefficientMap_upperStar {X T : Scheme.{u}} (f : X ⟶ T) :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).map (P.rootCoefficientMap h T) ≫
        Etale.upperStarForget₂Comparison P.Coefficient f (P.twistEtale h T) ≫
        (P.forgetEtale X).map (P.twistEtalePullback h f) =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf P.exponent f ≫
        P.rootCoefficientMap h X := by
  have hroot : P.rootPullback f =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf P.exponent f :=
    ((Classical.choose_spec (P.existsUnique_rootPullback f)).2 _
      (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι P.exponent f)).symm
  rw [← hroot]
  exact (Classical.choose_spec (P.existsUnique_twistEtalePullback h f)).1

/-- Naturality of the étale Kummer class. -/
theorem kummerEtale_upperStar {X T : Scheme.{u}} (f : X ⟶ T)
    (hT : IsUnit (P.exponent : Γ(T, ⊤))) (hX : IsUnit (P.exponent : Γ(X, ⊤)))
    (s : Γ(T, ⊤)ˣ) :
    ((P.kummerEtale h T hT s).mapExactFunctor
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f)).comp
        (Abelian.Ext.mk₀ (P.twistEtalePullback h f)) (add_zero 1) =
      (Abelian.Ext.mk₀ ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient)
        f).hom.app (ModuleCat.of P.Coefficient P.Coefficient))).comp
        (P.kummerEtale h X hX (Units.map f.appTop.hom s)) (zero_add 1) := by
  suffices key : (Abelian.Ext.mk₀ ((Scheme.upperStarConstantSheafIso
      (ModuleCat.{u + 1} P.Coefficient) f).inv.app (ModuleCat.of P.Coefficient P.Coefficient))).comp
      (((P.kummerEtale h T hT s).mapExactFunctor
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f)).comp
        (Abelian.Ext.mk₀ (P.twistEtalePullback h f)) (add_zero 1)) (zero_add 1) =
      P.kummerEtale h X hX (Units.map f.appTop.hom s) by
    rw [← key, Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id_app, Abelian.Ext.mk₀_id_comp]
  apply (P.moduleClassToAbelian_bijective X (P.twistEtale h X)).1
  rw [moduleClassToAbelian_kummerEtale,
    ← Scheme.sheafH_map_cohomologyMap_kummerδ₀ f P.exponent hT hX s,
    sheafH_map_map, ← rootCoefficientMap_upperStar, ← sheafH_map_map, ← sheafH_map_map,
    ← Etale.cohomologyMap_map, ← moduleClassToAbelian_kummerEtale P h T hT s]
  simp only [moduleClassToAbelian, Etale.cohomologyMap_apply, Sheaf.H.map_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  have hι : P.integerToConstant X ≫ (P.forgetEtale X).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
        (ModuleCat.of P.Coefficient P.Coefficient)) ≫
      (forgetUpperStarIso P f).inv.app (P.constantEtale T) =
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
        (AddCommGrpCat.of (ULift ℤ))).hom ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} f).map (P.integerToConstant T) := by
    rw [← cancel_epi ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app
      (AddCommGrpCat.of (ULift ℤ))), reassoc_of% (integerToConstant_upperStar P f)]
    simp only [Functor.comp_obj, forgetUpperStarIso, NatIso.ofComponents_inv_app, asIso_inv,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.app_hom, Iso.symm_hom,
      Iso.hom_inv_id_app_assoc]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, IsIso.hom_inv_id, Category.comp_id]
  rw [Abelian.Ext.mapExactFunctor_mapExactFunctor, Abelian.Ext.mapExactFunctor_mapExactFunctor,
    Abelian.Ext.mapExactFunctor_eq_of_iso (forgetUpperStarIso P f)]
  simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀_assoc, Abelian.Ext.mk₀_comp_mk₀]
  erw [hι]
  rfl

end KummerNaturality

end WeilConjectures.PurityFiniteSetting
