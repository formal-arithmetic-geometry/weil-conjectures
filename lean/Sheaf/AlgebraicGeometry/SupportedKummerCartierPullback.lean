/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.PicardTensorDualComparisonIso

/-!
# Cartier line bundle and canonical section under Cartier-preserving pullback

Source: Stacks Project, Tag 0C4U, lemma-pullback-effective-Cartier-divisors
(blueprint: lem-asd-supported-kummer-cartier-pullback).
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible

variable {T T' : Scheme.{u}}

/-- Canonical dual comparison for the pullback of the structure sheaf, obtained from the
transpose-of-evaluation comparison.

Source: Stacks Project, Tags 0096 (pullback of the structure sheaf) and 0FNV/01C8
(base change for duals of finite locally free modules).
(blueprint: lem-asd-supported-kummer-cartier-pullback) -/
noncomputable def tensorPullbackUnitDualMap (h : T' ⟶ T) :
    (Modules.unit T')ᵛ ⟶ (Scheme.Modules.tensorPullback h).obj (Modules.unit T)ᵛ := by
  letI : IsIso (Modules.picardTensorDualComparison h (Modules.unit T)) :=
    AlgebraicGeometry.Scheme.picardTensorDualComparison_isIso h (Modules.unit T)
  exact Modules.dualMap (Scheme.Modules.tensorPullbackObjUnitToUnit h) ≫
    (asIso (Modules.picardTensorDualComparison h (Modules.unit T))).inv

set_option backward.isDefEq.respectTransparency false in
private theorem exists_pullback_ideal_iso (g : T' ⟶ T)
    {J : T.IdealSheafData} (hJ : J.IsInvertible) (hJ' : (J.comap g).IsInvertible) :
    ∃ e : (Modules.pullback g).obj J.toModules ≅ (J.comap g).toModules,
      e.hom ≫ (J.comap g).toModulesι = J.pullbackToModulesι g := by
  have := hJ.isInvertible_toModules
  have := Modules.IsInvertible.sheafOfModules_isInvertible ((Modules.pullback g).obj J.toModules)
  let φ : (Modules.pullback g).obj J.toModules ⟶ (J.comap g).toModules :=
    kernel.lift _ (J.pullbackToModulesι g) (J.pullbackToModulesι_comp_toPushforwardSubscheme g)
  have hφ : φ ≫ (J.comap g).toModulesι = J.pullbackToModulesι g := kernel.lift_ι _ _ _
  have hi : IsIso φ := by
    refine Modules.isIso_of_isFreeGenerator φ fun y ↦ ?_
    obtain ⟨U, hyU, b, -, hU⟩ := hJ (g y)
    obtain ⟨s, hs⟩ := J.exists_toModulesι_app_eq (hU ▸ Ideal.mem_span_singleton_self b)
    obtain ⟨V, hyV, hVU, e, he⟩ :=
      Modules.exists_isFreeGenerator ((Modules.pullback g).obj J.toModules) (W := g ⁻¹ᵁ U.1) hyU
    obtain ⟨a, ha⟩ := he.exists_smul_eq (((Modules.pullback g).obj J.toModules).presheaf.map
      (homOfLE hVU).op (((Modules.pullbackPushforwardAdjunction g).unit.app J.toModules).app U.1 s))
    have hV : (J.comap g).ideal V =
        Ideal.span {T'.presheaf.map (homOfLE hVU).op (g.app U.1 b)} := by
      rw [J.ideal_comap_appLE g U V hVU, hU, Ideal.map_span, Set.image_singleton]
      rfl
    obtain ⟨a', ha'⟩ : ∃ a' : Γ(T', V.1), a' * T'.presheaf.map (homOfLE hVU).op (g.app U.1 b) =
        (J.comap g).toModulesι.app V.1 (φ.app V.1 e) :=
      Ideal.mem_span_singleton'.1 (by
        rw [← hV]
        exact ((J.comap g).range_toModulesι_app V).subset ⟨_, rfl⟩)
    have h1 := congrArg ((J.pullbackToModulesι g).app V.1) ha
    rw [Modules.Hom.app_smul, Modules.Hom.app_presheaf_map, pullbackToModulesι_app_unit, hs,
      ← hφ, Modules.Hom.comp_app] at h1
    rw [ConcreteCategory.comp_apply, ← ha'] at h1
    have haa' : a * a' = 1 := by
      have h2 : (a * a' - 1) * T'.presheaf.map (homOfLE hVU).op (g.app U.1 b) = 0 := by
        rw [sub_mul, one_mul, mul_assoc]
        exact sub_eq_zero.2 h1
      exact sub_eq_zero.1 (mem_nonZeroDivisors_iff_right.1 (hJ'.mem_nonZeroDivisors hV) _ h2)
    refine ⟨V.1, e, hyV, he, hJ'.isFreeGenerator _ fun V' h ↦ ?_⟩
    rw [← ha', map_mul, Ideal.span_singleton_mul_left_unit
      ((IsUnit.of_mul_eq_one a (mul_comm a a' ▸ haa')).map _), ← (J.comap g).map_ideal h, hV,
      Ideal.map_span, Set.image_singleton]
    rfl
  exact ⟨asIso φ, hφ⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_unit_comparison (h : T' ⟶ T) :
    (Modules.picardTensorComparison h).hom.app (Modules.unit T) ≫
      (Modules.pullbackObjUnitIso h).hom = Modules.tensorPullbackObjUnitToUnit h := by
  apply (Classical.choose (Modules.exists_tensorPullbackAdjunction h)).homEquiv _ _
    |>.injective
  rw [Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_apply]
  simp only [← Adjunction.homEquiv_apply, Modules.tensorPullbackObjUnitToUnit,
    Equiv.apply_symm_apply]
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    h.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency false in
private theorem exists_tensor_ideal_iso (h : T' ⟶ T)
    {J : T.IdealSheafData} (hJ : J.IsInvertible) (hJ' : (J.comap h).IsInvertible) :
    ∃ e : (Modules.tensorPullback h).obj J.toModules ≅ (J.comap h).toModules,
      e.hom ≫ (J.comap h).toModulesι =
        (Modules.tensorPullback h).map J.toModulesι ≫
          Modules.tensorPullbackObjUnitToUnit h := by
  obtain ⟨e, he⟩ := exists_pullback_ideal_iso h hJ hJ'
  refine ⟨(Modules.picardTensorComparison h).app J.toModules ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Category.assoc, he, IdealSheafData.pullbackToModulesι]
  erw [← (Modules.picardTensorComparison h).hom.naturality_assoc]
  rw [tensor_unit_comparison]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem tensor_obj_inv_naturality (h : T' ⟶ T)
    {A B C D : T.Modules} (f : A ⟶ B) (g : C ⟶ D) :
    ((Modules.tensorPullback h).map f ⊗ₘ (Modules.tensorPullback h).map g) ≫
        (Modules.picardTensorObjIso h B D).inv =
      (Modules.picardTensorObjIso h A C).inv ≫ (Modules.tensorPullback h).map (f ⊗ₘ g) := by
  simp only [Modules.picardTensorObjIso, Iso.trans_inv, Iso.symm_inv, tensorIso_inv]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  erw [(Modules.picardTensorComparison h).hom.naturality f,
    (Modules.picardTensorComparison h).hom.naturality g]
  rw [← tensorHom_comp_tensorHom_assoc, Functor.Monoidal.μIso_hom,
    Functor.LaxMonoidal.μ_natural_assoc]
  erw [(Modules.picardTensorComparison h).inv.naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_dual_naturality (h : T' ⟶ T) {M N : T.Modules} (f : M ⟶ N) :
    (Modules.tensorPullback h).map (Modules.dualMap f) ≫
        Modules.picardTensorDualComparison h M =
      Modules.picardTensorDualComparison h N ≫
        Modules.dualMap ((Modules.tensorPullback h).map f) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, Modules.picardTensorDualComparison,
    MonoidalClosed.uncurry_curry]
  have hp : Modules.dualMap ((Modules.tensorPullback h).map f) =
      (MonoidalClosed.pre ((Modules.tensorPullback h).map f)).app (Modules.unit T') :=
    (Modules.pre_app _ _).symm
  rw [hp, MonoidalClosed.uncurry_pre_app,
    Modules.picardTensorDualComparison, MonoidalClosed.uncurry_curry]
  rw [← id_tensorHom, ← (Modules.tensorPullback h).map_id,
    tensor_obj_inv_naturality_assoc]
  rw [← Functor.map_comp_assoc]
  have hp' : Modules.dualMap f =
      (MonoidalClosed.pre f).app (Modules.unit T) := (Modules.pre_app _ _).symm
  rw [hp', id_tensorHom, MonoidalClosed.id_tensor_pre_app_comp_ev]
  rw [Functor.map_comp, Category.assoc]
  have hn := tensor_obj_inv_naturality_assoc h f (𝟙 Nᵛ)
    ((Modules.tensorPullback h).map ((ihom.ev N).app (Modules.unit T)) ≫
      (Modules.picardTensorUnitIso h).hom)
  erw [CategoryTheory.Functor.map_id, tensorHom_id] at hn
  rw [tensorHom_id] at hn
  exact hn.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The Cartier line bundle and its canonical section pull back along a morphism whose
scheme-theoretic inverse-image ideal is again invertible.

The displayed dual-map equality is the canonical-section clause: the dual of the ideal inclusion
is preserved after the tensor pullback and the structure-sheaf identification. The proof follows
Stacks Tag 0C4U by local regular equations, the ideal-image base-change statement, and gluing;
all proof steps are recorded in the DAG node `lem-asd-supported-kummer-cartier-pullback`.
(blueprint: lem-asd-supported-kummer-cartier-pullback) -/
theorem exists_tensorPullback_dual_toModules_iso
    (h : T' ⟶ T) {J : T.IdealSheafData} (hJ : J.IsInvertible)
    (hJ' : (J.comap h).IsInvertible) :
    ∃ e : (Scheme.Modules.tensorPullback h).obj J.toModulesᵛ ≅ (J.comap h).toModulesᵛ,
      tensorPullbackUnitDualMap h ≫
          (Scheme.Modules.tensorPullback h).map (Modules.dualMap J.toModulesι) ≫ e.hom =
        Modules.dualMap (J.comap h).toModulesι := by
  have := hJ.isInvertible_toModules
  have := Modules.IsInvertible.sheafOfModules_isInvertible J.toModules
  have : IsIso (Modules.picardTensorDualComparison h J.toModules) :=
    Scheme.picardTensorDualComparison_isIso h J.toModules
  have : IsIso (Modules.picardTensorDualComparison h (Modules.unit T)) :=
    Scheme.picardTensorDualComparison_isIso h (Modules.unit T)
  obtain ⟨a, ha⟩ := exists_tensor_ideal_iso h hJ hJ'
  let b := (Modules.dualFunctor T').mapIso a.symm.op
  refine ⟨asIso (Modules.picardTensorDualComparison h J.toModules) ≪≫ b, ?_⟩
  dsimp only [tensorPullbackUnitDualMap, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc ((Modules.tensorPullback h).map (Modules.dualMap J.toModulesι)),
    tensor_dual_naturality]
  simp only [Category.assoc, asIso_inv, IsIso.inv_hom_id_assoc]
  change Modules.dualMap (Modules.tensorPullbackObjUnitToUnit h) ≫
    Modules.dualMap ((Modules.tensorPullback h).map J.toModulesι) ≫
      Modules.dualMap a.inv = _
  have hc : a.inv ≫ (Modules.tensorPullback h).map J.toModulesι ≫
      Modules.tensorPullbackObjUnitToUnit h = (J.comap h).toModulesι := by
    rw [← ha]
    simp only [← Category.assoc, a.inv_hom_id, Category.id_comp]
  change (Modules.dualFunctor T').map (Modules.tensorPullbackObjUnitToUnit h).op ≫
    (Modules.dualFunctor T').map ((Modules.tensorPullback h).map J.toModulesι).op ≫
      (Modules.dualFunctor T').map a.inv.op =
        (Modules.dualFunctor T').map (J.comap h).toModulesι.op
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  apply congrArg (fun f : (J.comap h).toModules ⟶ Modules.unit T' ↦
    (Modules.dualFunctor T').map f.op)
  exact hc

end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
