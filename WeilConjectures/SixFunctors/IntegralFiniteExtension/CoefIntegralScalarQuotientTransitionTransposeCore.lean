/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefScalarReductionExchange
public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionModels

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # Core mate calculation for scalar quotient transitions

Source: current blueprint, lem-sf-integral-scalar-quotient-transition, proof step 2.
(blueprint: lem-sf-integral-scalar-quotient-transition-transpose-core)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

private theorem derivedComp_change
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {F F' : A ⥤ B} (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [F'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ F') (a : F ⋙ G ≅ H) (b : F' ⋙ G ≅ H)
    (h : a = Functor.isoWhiskerRight e G ≪≫ b) :
    (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
        Functor.mapDerivedCategoryNatIso a =
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso e) G.mapDerivedCategory ≪≫
        (Functor.mapDerivedCategoryCompIso F' G).symm ≪≫
          Functor.mapDerivedCategoryNatIso b := by
  apply Iso.ext
  rw [h]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapDerivedCategoryNatIso_trans]
  have hc := Functor.mapDerivedCategoryNatIso_isoWhiskerRight e G
  have hc' : (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e G)).hom =
      (Functor.mapDerivedCategoryCompIso F G).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom G.mapDerivedCategory ≫
          (Functor.mapDerivedCategoryCompIso F' G).inv := by
    rw [← reassoc_of% hc]
    simp only [Iso.hom_inv_id, Category.comp_id]
  rw [hc']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.isoWhiskerRight_hom]

private theorem eqIso_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F F' : A ⥤ B} (G : B ⥤ C) {H : A ⥤ C}
    (h : F = F') (h' : F' ⋙ G = H) (h'' : F ⋙ G = H) :
    eqToIso h'' = Functor.isoWhiskerRight (eqToIso h) G ≪≫ eqToIso h' := by
  subst F'
  subst H
  apply Iso.ext
  ext K
  simp

private theorem uniq_transpose
    {C A : Type*} [Category C] [Category A]
    {F F' : C ⥤ A} {R R' : A ⥤ C}
    (a : F ⊣ R) (b : F' ⊣ R') (e : R ≅ R')
    (K : C) (N : A) (f : F'.obj K ⟶ N) :
    a.homEquiv K N ((((a.ofNatIsoRight e).leftAdjointUniq b).hom.app K) ≫ f) =
      b.homEquiv K N f ≫ e.inv.app N := by
  apply (cancel_mono (e.hom.app N)).1
  rw [← Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.homEquiv_unit, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

private theorem uniq_inv_transpose
    {C A : Type*} [Category C] [Category A]
    {F F' : C ⥤ A} {R R' : A ⥤ C}
    (a : F ⊣ R) (b : F' ⊣ R') (e : R ≅ R')
    (K : C) (N : A) (f : F.obj K ⟶ N) :
    b.homEquiv K N ((((a.ofNatIsoRight e).leftAdjointUniq b).inv.app K) ≫ f) =
      a.homEquiv K N f ≫ e.hom.app N := by
  have hh := uniq_transpose a b e K N
    (((a.ofNatIsoRight e).leftAdjointUniq b).inv.app K ≫ f)
  simp only [Iso.hom_inv_id_app_assoc] at hh
  have hh' := congrArg (fun k ↦ k ≫ e.hom.app N) hh
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hh'.symm

private theorem uniq_same_transpose
    {C A : Type*} [Category C] [Category A]
    {F F' : C ⥤ A} {R : A ⥤ C}
    (a : F ⊣ R) (b : F' ⊣ R) (K : C) (N : A) (f : F'.obj K ⟶ N) :
    a.homEquiv K N ((a.leftAdjointUniq b).hom.app K ≫ f) =
      b.homEquiv K N f := by
  rw [a.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    b.homEquiv_unit]

private theorem uniq_same_inv_transpose
    {C A : Type*} [Category C] [Category A]
    {F F' : C ⥤ A} {R : A ⥤ C}
    (a : F ⊣ R) (b : F' ⊣ R) (K : C) (N : A) (f : F.obj K ⟶ N) :
    b.homEquiv K N ((a.leftAdjointUniq b).inv.app K ≫ f) =
      a.homEquiv K N f := by
  rw [Adjunction.leftAdjointUniq_inv_app, uniq_same_transpose]

private theorem normalized_square_unit
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {F : C ⥤ D} {U : D ⥤ C}
    {P₀ P : C ⥤ A} {V : A ⥤ C} {Q₀ Q : D ⥤ B} {W : B ⥤ D}
    {T : A ⥤ B} {R : B ⥤ A} {H : C ⥤ B} {Z : B ⥤ C}
    (a : F ⊣ U) (p₀ : P₀ ⊣ V) (p : P ⊣ V)
    (q₀ : Q₀ ⊣ W) (q : Q ⊣ W) (t : T ⊣ R) (d : H ⊣ Z)
    (α : R ⋙ V ≅ Z) (β : W ⋙ U ≅ Z) (K : C) :
    a.homEquiv _ _ (q.homEquiv _ _
      ((q₀.leftAdjointUniq q).inv.app (F.obj K) ≫
        ((((a.comp q₀).ofNatIsoRight β).leftAdjointUniq d).hom.app K ≫
          (((p₀.comp t).ofNatIsoRight α).leftAdjointUniq d).inv.app K) ≫
        T.map ((p₀.leftAdjointUniq p).hom.app K))) =
      p.unit.app K ≫ V.map (t.unit.app (P.obj K)) ≫
        α.hom.app (T.obj (P.obj K)) ≫ β.inv.app (T.obj (P.obj K)) := by
  simp only [Category.assoc]
  rw [uniq_same_inv_transpose]
  rw [← Equiv.trans_apply,
    ← congrFun (congrFun (Adjunction.comp_homEquiv a q₀) K) _]
  erw [uniq_transpose (a.comp q₀) d β K _ _,
    uniq_inv_transpose (p₀.comp t) d α K _ _]
  have hh : (p₀.comp t).homEquiv _ _ (T.map ((p₀.leftAdjointUniq p).hom.app K)) =
      p.unit.app K ≫ V.map (t.unit.app (P.obj K)) := by
    rw [Adjunction.comp_homEquiv]
    change p₀.homEquiv K _ (t.homEquiv _ _
      (T.map ((p₀.leftAdjointUniq p).hom.app K))) = _
    rw [t.homEquiv_unit]
    have ht := t.unit.naturality ((p₀.leftAdjointUniq p).hom.app K)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at ht
    rw [← ht, uniq_same_transpose, p.homEquiv_unit]
  rw [hh]
  simp only [Category.assoc]

private theorem mixed_unit_named
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {T : A ⥤ B} {R : B ⥤ A} {T' : C ⥤ D} {R' : D ⥤ C}
    (a : T ⊣ R) (b : T' ⊣ R') (F : A ⥤ C) (G : B ⥤ D)
    (s : R ⋙ F ⟶ G ⋙ R') (z : F ⋙ T' ⟶ T ⋙ G)
    (hz : z = ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ s)).natTrans) (M : A) :
    b.unit.app (F.obj M) ≫ R'.map (z.app M) =
      F.map (a.unit.app M) ≫ s.app (T.obj M) := by
  rw [hz]
  exact (unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ s) M).symm

private theorem comparison_postcompose
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {F : C ⥤ D} {U : D ⥤ C} {P : C ⥤ A} {V : A ⥤ C}
    {Q : D ⥤ B} {W : B ⥤ D} {T : A ⥤ B} {R : B ⥤ A}
    (a : F ⊣ U) (p : P ⊣ V) (q : Q ⊣ W) (t : T ⊣ R)
    (d : R ⋙ V ≅ W ⋙ U) (K : C)
    (c : Q.obj (F.obj K) ⟶ T.obj (P.obj K))
    (hc : a.homEquiv _ _ (q.homEquiv _ _ c) =
      p.unit.app K ≫ V.map (t.unit.app (P.obj K)) ≫ d.hom.app (T.obj (P.obj K)))
    {N : B} (f : T.obj (P.obj K) ⟶ N) :
    a.homEquiv _ _ (q.homEquiv _ _ (c ≫ f)) =
      p.unit.app K ≫ V.map (t.homEquiv _ _ f) ≫ d.hom.app N := by
  rw [q.homEquiv_naturality_right, a.homEquiv_naturality_right, hc]
  have hn := d.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← hn]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private def cubeCondition
    {C D A B A' B' : Type*}
    [Category C] [Category D] [Category A] [Category B] [Category A'] [Category B']
    (U : D ⥤ C) (Vm : A ⥤ C) (Vn : B ⥤ C) (Wm : A' ⥤ D) (Wn : B' ⥤ D)
    (Rm : A' ⥤ A) (Rn : B' ⥤ B) (S : B ⥤ A) (S' : B' ⥤ A')
    (e : S ⋙ Vm ≅ Vn) (e' : S' ⋙ Wm ≅ Wn)
    (dm : Rm ⋙ Vm ≅ Wm ⋙ U) (dn : Rn ⋙ Vn ≅ Wn ⋙ U)
    (z : Rn ⋙ S ⟶ S' ⋙ Rm) : Prop :=
  Functor.whiskerLeft Rn e.inv ≫ Functor.whiskerRight z Vm ≫
    Functor.whiskerLeft S' dm.hom = dn.hom ≫ Functor.whiskerRight e'.inv U

private theorem restriction_transition_calculation
    {C D A B A' B' : Type*}
    [Category C] [Category D] [Category A] [Category B] [Category A'] [Category B']
    (U : D ⥤ C) (Vm : A ⥤ C) (Vn : B ⥤ C) (Wm : A' ⥤ D) (Wn : B' ⥤ D)
    (Rm : A' ⥤ A) (Rn : B' ⥤ B) (S : B ⥤ A) (S' : B' ⥤ A')
    (e : S ⋙ Vm ≅ Vn) (e' : S' ⋙ Wm ≅ Wn)
    (dm : Rm ⋙ Vm ≅ Wm ⋙ U) (dn : Rn ⋙ Vn ≅ Wn ⋙ U)
    (s : Rn ⋙ S ⟶ S' ⋙ Rm)
    (hcube : cubeCondition U Vm Vn Wm Wn Rm Rn S S' e e' dm dn s)
    {K : C} {M : A} {P : B} {N : B'}
    (p : K ⟶ Vm.obj M) (q : K ⟶ Vn.obj P)
    (τ : M ⟶ S.obj P) (f : P ⟶ Rn.obj N)
    (hτ : p ≫ Vm.map τ = q ≫ e.inv.app P) :
    p ≫ Vm.map (τ ≫ S.map f ≫ s.app N) ≫ dm.hom.app (S'.obj N) =
      q ≫ Vn.map f ≫ dn.hom.app N ≫ U.map (e'.inv.app N) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc p, hτ]
  simp only [Category.assoc]
  have he := e.inv.naturality f
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at he
  rw [← Category.assoc (e.inv.app P), ← he]
  simp only [Category.assoc]
  unfold cubeCondition at hcube
  have hc := NatTrans.congr_app hcube N
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hc
  rw [hc]

private theorem transition_unit_named
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Pm : C ⥤ A} {Vm : A ⥤ C} {Pn : C ⥤ B} {Vn : B ⥤ C}
    (pm : Pm ⊣ Vm) (pn : Pn ⊣ Vn) (S : B ⥤ A) (e : S ⋙ Vm ≅ Vn)
    (M : C) (τ : Pm.obj M ⟶ S.obj (Pn.obj M))
    (hτ : τ = (pm.homEquiv _ _).symm (pn.unit.app M ≫ e.inv.app (Pn.obj M))) :
    pm.homEquiv _ _ τ = pn.unit.app M ≫ e.inv.app (Pn.obj M) := by
  rw [hτ]
  exact (pm.homEquiv M _).apply_symm_apply _

private theorem transition_natural
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Pm : C ⥤ A} {Vm : A ⥤ C} {Pn : C ⥤ B} {Vn : B ⥤ C}
    (pm : Pm ⊣ Vm) (pn : Pn ⊣ Vn) (S : B ⥤ A) (e : S ⋙ Vm ≅ Vn)
    {K M : C} (f : K ⟶ M) :
    Pm.map f ≫ (pm.homEquiv _ _).symm (pn.unit.app M ≫ e.inv.app (Pn.obj M)) =
      (pm.homEquiv _ _).symm (pn.unit.app K ≫ e.inv.app (Pn.obj K)) ≫
        S.map (Pn.map f) := by
  apply (pm.homEquiv _ _).injective
  rw [pm.homEquiv_naturality_left, pm.homEquiv_naturality_right]
  dsimp only [Functor.id_obj]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hu := pn.unit.naturality f
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, hu]
  have hn := e.inv.naturality (Pn.map f)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [hn]

private theorem transition_transpose
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Pm : C ⥤ A} {Vm : A ⥤ C} {Pn : C ⥤ B} {Vn : B ⥤ C}
    (pm : Pm ⊣ Vm) (pn : Pn ⊣ Vn) (S : B ⥤ A) (e : S ⋙ Vm ≅ Vn)
    (K : C) {N : B} (f : Pn.obj K ⟶ N) :
    pm.homEquiv _ _
        ((pm.homEquiv _ _).symm (pn.unit.app K ≫ e.inv.app (Pn.obj K)) ≫ S.map f) =
      pn.unit.app K ≫ pm.homEquiv _ _
        (Pm.map (e.inv.app (Pn.obj K)) ≫ pm.counit.app (S.obj (Pn.obj K)) ≫ S.map f) := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [pm.homEquiv_naturality_left]

private theorem transported_transpose
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Pm : C ⥤ A} {Vm : A ⥤ C} {Pn : C ⥤ B} {Vn : B ⥤ C}
    (pm : Pm ⊣ Vm) (pn : Pn ⊣ Vn) (S : B ⥤ A) (e : S ⋙ Vm ≅ Vn)
    {K M : C} {N : B} (f : K ⟶ M) (g : Pm.obj M ⟶ S.obj N)
    (c : Pn.obj M ⟶ N)
    (hg : g = (pm.homEquiv _ _).symm
      (pn.unit.app M ≫ e.inv.app (Pn.obj M)) ≫ S.map c) :
    pm.homEquiv _ _ (Pm.map f ≫ g) =
      pn.unit.app K ≫ pm.homEquiv _ _
        (Pm.map (e.inv.app (Pn.obj K)) ≫ pm.counit.app (S.obj (Pn.obj K)) ≫
          S.map (Pn.map f ≫ c)) := by
  rw [hg]
  have hn := transition_natural pm pn S e f
  dsimp only [Functor.id_obj, Functor.comp_obj] at hn ⊢
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  simpa only [Functor.id_obj, Functor.comp_obj] using
    transition_transpose pm pn S e K (Pn.map f ≫ c)

private theorem transported_transpose_named
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Pm : C ⥤ A} {Vm : A ⥤ C} {Pn : C ⥤ B} {Vn : B ⥤ C}
    (pm : Pm ⊣ Vm) (pn : Pn ⊣ Vn) (S : B ⥤ A) (e : S ⋙ Vm ≅ Vn)
    {K M : C} {N : B} (f : K ⟶ M) (g : Pm.obj M ⟶ S.obj N)
    (c : Pn.obj M ⟶ N) (τ : Pm.obj M ⟶ S.obj (Pn.obj M))
    (hτ : τ = (pm.homEquiv _ _).symm (pn.unit.app M ≫ e.inv.app (Pn.obj M)))
    (hg : g = τ ≫ S.map c) :
    pm.homEquiv _ _ (Pm.map f ≫ g) =
      pn.unit.app K ≫ pm.homEquiv _ _
        (Pm.map (e.inv.app (Pn.obj K)) ≫ pm.counit.app (S.obj (Pn.obj K)) ≫
          S.map (Pn.map f ≫ c)) := by
  apply transported_transpose pm pn S e f g c
  rw [← hτ]
  exact hg

private theorem whiskerRight_comp_heq
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F G : A ⥤ C} (h : F = G) {H I : B ⥤ C} (h' : H = I)
    {S T : B ⥤ A} (q : S ≅ T) (d : T ⋙ F ≅ H) (d' : T ⋙ G ≅ I)
    (hd : HEq d d') :
    HEq (Functor.isoWhiskerRight q F ≪≫ d) (Functor.isoWhiskerRight q G ≪≫ d') := by
  subst G
  subst I
  cases hd
  rfl

private theorem cube_transfer_heq
    {C D A B A' B' : Type*}
    [Category C] [Category D] [Category A] [Category B] [Category A'] [Category B']
    {U : D ⥤ C} {Vm Vm₀ : A ⥤ C} {Vn Vn₀ : B ⥤ C}
    {Wm Wm₀ : A' ⥤ D} {Wn Wn₀ : B' ⥤ D}
    {Rm : A' ⥤ A} {Rn : B' ⥤ B} {S : B ⥤ A} {S' : B' ⥤ A'}
    (hVm : Vm = Vm₀) (hVn : Vn = Vn₀) (hWm : Wm = Wm₀) (hWn : Wn = Wn₀)
    {e : S ⋙ Vm ≅ Vn} {e₀ : S ⋙ Vm₀ ≅ Vn₀}
    {e' : S' ⋙ Wm ≅ Wn} {e₀' : S' ⋙ Wm₀ ≅ Wn₀}
    {dm : Rm ⋙ Vm ≅ Wm ⋙ U} {dm₀ : Rm ⋙ Vm₀ ≅ Wm₀ ⋙ U}
    {dn : Rn ⋙ Vn ≅ Wn ⋙ U} {dn₀ : Rn ⋙ Vn₀ ≅ Wn₀ ⋙ U}
    {z : Rn ⋙ S ⟶ S' ⋙ Rm}
    (he : HEq e e₀) (he' : HEq e' e₀') (hdm : HEq dm dm₀) (hdn : HEq dn dn₀)
    (hc : cubeCondition U Vm₀ Vn₀ Wm₀ Wn₀ Rm Rn S S' e₀ e₀' dm₀ dn₀ z) :
    cubeCondition U Vm Vn Wm Wn Rm Rn S S' e e' dm dn z := by
  subst Vm₀
  subst Vn₀
  subst Wm₀
  subst Wn₀
  cases he
  cases he'
  cases hdm
  cases hdn
  exact hc

private theorem ordinaryCompletedComp_eq
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (f : R ⟶ S) (g : S ⟶ T) (r : R ⟶ T)
    (h : f ≫ g = r)
    (hF : SheafOfModules.restrictScalars.{u + 1} g ⋙
      SheafOfModules.restrictScalars.{u + 1} f = SheafOfModules.restrictScalars.{u + 1} r) :
    normalizedDVRRestrictionCompIso f g ≪≫
        eqToIso (congrArg (fun z ↦ SheafOfModules.restrictScalars.{u + 1} z) h) =
      eqToIso hF := by
  change Iso.refl _ ≪≫ eqToIso _ = _
  simp only [Iso.refl_trans]

attribute [local irreducible] scalarReductionDerivedExtension
  integralScalarExtensionOfUniverses quotient normalizedDVRReductionTransition
  scalarReductionExchange

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The residual finite reduction comparison, with the completion transport removed.

This is the finite tensor and reduction part of the transpose calculation.  The
remaining mate calculation is supplied by the theorem below.  It is separated
from the completion isomorphism because the latter is handled by adjunction
naturality in the parent theorem.

Source: lem-sf-integral-scalar-quotient-transition, proof step 2.
(blueprint: lem-sf-integral-scalar-quotient-transition-transpose-core)
-/
def quotientResidual (K : IntegralVerdier.Ambient l E X) (j : ℕ) :
    (scalarReductionDerivedExtension l L X j).obj
        ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K) ≅
      (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X j)).obj
        ((scalarReductionDerivedExtension l E X j).obj K) :=
  (PurCompactSupport.finiteReductionIso l L X j).symm.app _ ≪≫
    (PurCompactSupport.tensorSquare (completedCoefficientMap l E L ι X)
      (integralScalarQuotientSheafMap l E L ι X j)
      (completedIntegralCommRingProjectionUnrestricted l E X j)
      (completedIntegralCommRingProjectionUnrestricted l L X j)
      ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec j)).app K ≪≫
    (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X j)).mapIso
      ((PurCompactSupport.finiteReductionIso l E X j).app K)

private theorem finiteReduction_eq (j : ℕ) :
    PurCompactSupport.finiteReductionIso l E X j =
      (pbcDerivedScalarAdjunction
        (completedIntegralCommRingProjectionUnrestricted l E X j)).leftAdjointUniq
          (normalizedDVRIntegralAdjunction l E X j) := by
  unfold PurCompactSupport.finiteReductionIso normalizedDVRIntegralAdjunction
    PurCompactSupport.projection
  simp only [eqToHom_refl]
  rfl

private theorem scalarRestriction_eq (j : ℕ) :
    scalarReductionDerivedRestriction l E X j =
      pbcDerivedRestrict (completedIntegralCommRingProjectionUnrestricted l E X j) := by
  rfl

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence normalizedDVRIntegralAdjunction pbcDerivedScalarAdjunction
  AlgebraicGeometry.Scheme.reductionDerivedChange
  pbcDerivedRestrictComp PurCompactSupport.tensorSquare
  PurCompactSupport.finiteReductionIso Adjunction.leftAdjointUniq

private theorem restrict_assoc
    {W : Scheme.{u}} {R S B V : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : B ⟶ V)
    (ab : R ⟶ B) (bc : S ⟶ V) (abc : R ⟶ V)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc)
    (M : @DerivedCategory (pbcModules W V) _ _ (HasDerivedCategory.standard _)) :
    (pbcDerivedRestrict a).map ((pbcDerivedRestrictComp b c bc hbc).hom.app M) ≫
        (pbcDerivedRestrictComp a bc abc hr).hom.app M =
      (pbcDerivedRestrictComp a b ab hab).hom.app ((pbcDerivedRestrict c).obj M) ≫
        (pbcDerivedRestrictComp ab c abc hl).hom.app M := by
  letI : HasDerivedCategory (pbcModules W R) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (pbcModules W S) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (pbcModules W B) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (pbcModules W V) := HasDerivedCategory.standard _
  have ho (N : pbcModules W V) :
      (pbcRestrict a).map ((pbcRestrictComp b c bc hbc).hom.app N) ≫
          (pbcRestrictComp a bc abc hr).hom.app N =
        (pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj N) ≫
          (pbcRestrictComp ab c abc hl).hom.app N := by
    ext U x
    change ((pbcRestrictComp a bc abc hr).hom.app N).val.app U
        (((pbcRestrictComp b c bc hbc).hom.app N).val.app U x) =
      ((pbcRestrictComp ab c abc hl).hom.app N).val.app U
        (((pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj N)).val.app U x)
    simp only [pbcRestrictComp, (pbcRestrictComp_exists a bc abc hr).exists.choose_spec,
      (pbcRestrictComp_exists b c bc hbc).exists.choose_spec,
      (pbcRestrictComp_exists ab c abc hl).exists.choose_spec,
      (pbcRestrictComp_exists a b ab hab).exists.choose_spec]
  have hd := Functor.mapDerivedCategoryCompNatIso_cocycle
    (pbcRestrictComp b c bc hbc) (pbcRestrictComp a bc abc hr)
    (pbcRestrictComp a b ab hab) (pbcRestrictComp ab c abc hl) ho M
  unfold pbcDerivedRestrictComp pbcDerivedRestrict
  simpa only [Functor.mapDerivedCategoryCompNatIso, Functor.comp_obj] using hd

private theorem restriction_cube
    {W : Scheme.{u}} {R S A B A' B' : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (p : R ⟶ A) (q : A ⟶ B) (r : R ⟶ B)
    (s : S ⟶ A') (t : A' ⟶ B') (v : S ⟶ B')
    (b : A ⟶ A') (c : B ⟶ B')
    (hm : a ≫ s = p ≫ b) (hn : a ≫ v = r ≫ c)
    (hE : p ≫ q = r) (hL : s ≫ t = v) (hQ : b ≫ t = q ≫ c)
    (N : @DerivedCategory (pbcModules W B') _ _ (HasDerivedCategory.standard _)) :
    (pbcDerivedRestrictComp p q r hE).inv.app ((pbcDerivedRestrict c).obj N) ≫
        (pbcDerivedRestrict p).map
          ((pbcDerivedRestrictComp q c (b ≫ t) hQ.symm).hom.app N ≫
            (pbcDerivedRestrictComp b t (b ≫ t) rfl).inv.app N) ≫
        (pbcDerivedRestrictComp p b (a ≫ s) hm.symm).hom.app
          ((pbcDerivedRestrict t).obj N) ≫
        (pbcDerivedRestrictComp a s (a ≫ s) rfl).inv.app
          ((pbcDerivedRestrict t).obj N) =
      (pbcDerivedRestrictComp r c (a ≫ v) hn.symm).hom.app N ≫
        (pbcDerivedRestrictComp a v (a ≫ v) rfl).inv.app N ≫
        (pbcDerivedRestrict a).map ((pbcDerivedRestrictComp s t v hL).inv.app N) := by
  have hdt : (a ≫ s) ≫ t = a ≫ v := by rw [Category.assoc, hL]
  have hpc : p ≫ (b ≫ t) = a ≫ v := by rw [← Category.assoc, ← hm, hdt]
  have h₁ := restrict_assoc p q c r (b ≫ t) (a ≫ v) hE hQ.symm hn.symm hpc N
  have h₂ := restrict_assoc p b t (a ≫ s) (b ≫ t) (a ≫ v)
    hm.symm rfl hdt hpc N
  have h₃ := restrict_assoc a s t (a ≫ s) v (a ≫ v) rfl hL hdt rfl N
  let z := (pbcDerivedRestrictComp a s (a ≫ s) rfl).app
      ((pbcDerivedRestrict t).obj N) ≪≫
    (pbcDerivedRestrictComp (a ≫ s) t (a ≫ v) hdt).app N
  apply (Iso.cancel_iso_hom_right _ _ z).1
  dsimp only [z, Iso.trans_hom, Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← h₂]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [h₁]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← h₃]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem projection_quotient {m n : ℕ} (h : n ≤ m) :
    completedIntegralCommRingProjectionUnrestricted l E X m ≫ scalarQuotient l E X h =
      completedIntegralCommRingProjectionUnrestricted l E X n := by
  exact compactSupportProjection_comp l E X m n h

private theorem restriction_cube_transport
    {W : Scheme.{u}} {R S A B A' B' : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (p : R ⟶ A) (q : A ⟶ B) (r : R ⟶ B)
    (s : S ⟶ A') (t : A' ⟶ B') (v : S ⟶ B')
    (b : A ⟶ A') (c : B ⟶ B')
    (hm : a ≫ s = p ≫ b) (hn : a ≫ v = r ≫ c)
    (hE : p ≫ q = r) (hL : s ≫ t = v) (hQ : b ≫ t = q ≫ c)
    (S₀ : @DerivedCategory (pbcModules W B) _ _ (HasDerivedCategory.standard _) ⥤
      @DerivedCategory (pbcModules W A) _ _ (HasDerivedCategory.standard _))
    (S₀' : @DerivedCategory (pbcModules W B') _ _ (HasDerivedCategory.standard _) ⥤
      @DerivedCategory (pbcModules W A') _ _ (HasDerivedCategory.standard _))
    (hS : S₀ = pbcDerivedRestrict q) (hS' : S₀' = pbcDerivedRestrict t)
    :
    let e := pbcDerivedRestrictComp p q r hE
    let e' := pbcDerivedRestrictComp s t v hL
    let dm := pbcDerivedRestrictComp p b (a ≫ s) hm.symm ≪≫
      (pbcDerivedRestrictComp a s (a ≫ s) rfl).symm
    let dn := pbcDerivedRestrictComp r c (a ≫ v) hn.symm ≪≫
      (pbcDerivedRestrictComp a v (a ≫ v) rfl).symm
    let z := Functor.isoWhiskerLeft (pbcDerivedRestrict c) (eqToIso hS) ≪≫
      pbcDerivedRestrictComp q c (b ≫ t) hQ.symm ≪≫
      (pbcDerivedRestrictComp b t (b ≫ t) rfl).symm ≪≫
      Functor.isoWhiskerRight (eqToIso hS'.symm) (pbcDerivedRestrict b)
    cubeCondition (pbcDerivedRestrict a)
      (pbcDerivedRestrict p) (pbcDerivedRestrict r)
      (pbcDerivedRestrict s) (pbcDerivedRestrict v)
      (pbcDerivedRestrict b) (pbcDerivedRestrict c) S₀ S₀'
      (Functor.isoWhiskerRight (eqToIso hS) (pbcDerivedRestrict p) ≪≫ e)
      (Functor.isoWhiskerRight (eqToIso hS') (pbcDerivedRestrict s) ≪≫ e')
      dm dn z.hom := by
  subst S₀
  subst S₀'
  unfold cubeCondition
  dsimp only
  ext N
  simpa only [eqToIso_refl, Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl,
    Iso.refl_trans, Iso.trans_refl, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using
      restriction_cube a p q r s t v b c hm hn hE hL hQ N

private theorem restrict_comp_eqToIso
    {W : Scheme.{u}} {R S B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (f : R ⟶ S) (g : S ⟶ B) (k : R ⟶ B) (h : f ≫ g = k)
    (he : pbcRestrict g ⋙ pbcRestrict f = pbcRestrict k) :
    pbcRestrictComp f g k h = eqToIso he := by
  subst k
  apply (pbcRestrictComp_exists f g (f ≫ g) rfl).unique
  · exact (pbcRestrictComp_exists f g (f ≫ g) rfl).exists.choose_spec
  · intro M U x
    rfl

private theorem derived_eqToIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G] (h : F = G)
    (hd : F.mapDerivedCategory = G.mapDerivedCategory) :
    Functor.mapDerivedCategoryNatIso (eqToIso h) = eqToIso hd := by
  subst G
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

section CompletedComparison
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

private theorem completed_comp_eq {m n : ℕ} (h : n ≤ m) :
    normalizedDVRResCompletedComp l E X D hl h =
      Functor.isoWhiskerRight (eqToIso (scalarQuotient_restrict l E X h))
        (scalarReductionDerivedRestriction l E X m) ≪≫
      pbcDerivedRestrictComp (completedIntegralCommRingProjectionUnrestricted l E X m)
        (scalarQuotient l E X h) (completedIntegralCommRingProjectionUnrestricted l E X n)
        (projection_quotient l E X h) := by
  letI : HasDerivedCategory (scalarReductionSource l E X) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (scalarReductionTarget l E X m) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (scalarReductionTarget l E X n) := HasDerivedCategory.standard _
  let F := normalizedDVRModuleRes l E X h
  let F' := pbcRestrict (scalarQuotient l E X h)
  let G := scalarReductionRestriction l E X m
  let H := scalarReductionRestriction l E X n
  letI : F'.Additive := pbcRestrict_additive (scalarQuotient l E X h)
  letI : PreservesFiniteLimits F' := pbcRestrict_limits (scalarQuotient l E X h)
  letI : PreservesFiniteColimits F' := pbcRestrict_colimits (scalarQuotient l E X h)
  have hf : F = F' := finiteDualizingRestriction_eq l E X h
  have h₀ : F ⋙ G = H := coefficientRestrictionComp l E X h
  have h₁ : F' ⋙ G = H := (congrArg (fun f ↦ f ⋙ G) hf).symm.trans h₀
  have he : normalizedDVRResCompletedComp l E X D hl h =
      (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
        Functor.mapDerivedCategoryNatIso (eqToIso h₀) := by
    unfold normalizedDVRResCompletedComp
    dsimp only
    have hk := ordinaryCompletedComp_eq
      (completedIntegralCoefficientProjection l E X D hl m) (normalizedDVRQuotient l E X h)
      (completedIntegralCoefficientProjection l E X D hl n)
      (limit.w (integralCoefficientSheafSystem l E X) (homOfLE h).op) h₀
    erw [hk]
    rfl
  have he' : pbcDerivedRestrictComp
      (completedIntegralCommRingProjectionUnrestricted l E X m) (scalarQuotient l E X h)
      (completedIntegralCommRingProjectionUnrestricted l E X n)
      (projection_quotient l E X h) =
      (Functor.mapDerivedCategoryCompIso F' G).symm ≪≫
        Functor.mapDerivedCategoryNatIso (eqToIso h₁) := by
    unfold pbcDerivedRestrictComp
    rw [restrict_comp_eqToIso _ _ _ _ h₁]
  have ho : eqToIso h₀ = Functor.isoWhiskerRight (eqToIso hf) G ≪≫ eqToIso h₁ := by
    exact eqIso_comp G hf h₁ h₀
  rw [he, he', derivedComp_change G H (eqToIso hf) (eqToIso h₀) (eqToIso h₁) ho]
  rw [derived_eqToIso F F' hf (scalarQuotient_restrict l E X h)]
  rfl

end CompletedComparison

private def residualRestriction (j : ℕ) :
    pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X j) ⋙
        scalarReductionDerivedRestriction l E X j ≅
      scalarReductionDerivedRestriction l L X j ⋙
        pbcDerivedRestrict (completedCoefficientMap l E L ι X) :=
  pbcDerivedRestrictComp (completedIntegralCommRingProjectionUnrestricted l E X j)
      (integralScalarQuotientSheafMap l E L ι X j)
      (completedCoefficientMap l E L ι X ≫
        completedIntegralCommRingProjectionUnrestricted l L X j)
      ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec j).symm ≪≫
    (pbcDerivedRestrictComp (completedCoefficientMap l E L ι X)
      (completedIntegralCommRingProjectionUnrestricted l L X j) _ rfl).symm

section ResidualUnit
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

private theorem quotientResidual_unit (K : IntegralVerdier.Ambient l E X) (j : ℕ) :
    (pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X)).homEquiv _ _
        ((normalizedDVRIntegralAdjunction l L X j).homEquiv _ _
          (quotientResidual l E L ι X K j).hom) =
      (normalizedDVRIntegralAdjunction l E X j).unit.app K ≫
        (scalarReductionDerivedRestriction l E X j).map
          ((pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X j)).unit.app
            ((scalarReductionDerivedExtension l E X j).obj K)) ≫
        (residualRestriction l E L ι X j).hom.app
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X j)).obj
            ((scalarReductionDerivedExtension l E X j).obj K)) := by
  have hh := normalized_square_unit
      (V := scalarReductionDerivedRestriction l E X j)
      (W := scalarReductionDerivedRestriction l L X j)
      (pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X))
      (pbcDerivedScalarAdjunction (completedIntegralCommRingProjectionUnrestricted l E X j))
      (normalizedDVRIntegralAdjunction l E X j)
      (pbcDerivedScalarAdjunction (completedIntegralCommRingProjectionUnrestricted l L X j))
      (normalizedDVRIntegralAdjunction l L X j)
      (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X j))
      (pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X ≫
        completedIntegralCommRingProjectionUnrestricted l L X j))
      (pbcDerivedRestrictComp (completedIntegralCommRingProjectionUnrestricted l E X j)
        (integralScalarQuotientSheafMap l E L ι X j) _
        ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec j).symm)
      (pbcDerivedRestrictComp (completedCoefficientMap l E L ι X)
        (completedIntegralCommRingProjectionUnrestricted l L X j) _ rfl) K
  simp only [quotientResidual, residualRestriction, PurCompactSupport.tensorSquare,
    finiteReduction_eq, PurCompactSupport.tensorComposition,
    Iso.app, Iso.trans, Iso.symm, NatTrans.comp_app,
    Functor.mapIso] at hh ⊢
  exact hh

end ResidualUnit

private abbrev nativeDerived (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :=
  @DerivedCategory (pbcModules W R) _ _ (HasDerivedCategory.standard _)

section ResidualCube
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

private theorem residualRestriction_cube {m n : ℕ} (h : n ≤ m) :
    cubeCondition (C := nativeDerived X (completedIntegralCommRingSheafUnrestricted l E X))
      (D := nativeDerived X (completedIntegralCommRingSheafUnrestricted l L X))
      (A := nativeDerived X (integralCoefficientCommRingSheaf l E X m))
      (B := nativeDerived X (integralCoefficientCommRingSheaf l E X n))
      (A' := nativeDerived X (integralCoefficientCommRingSheaf l L X m))
      (B' := nativeDerived X (integralCoefficientCommRingSheaf l L X n))
      (pbcDerivedRestrict (completedCoefficientMap l E L ι X))
      (scalarReductionDerivedRestriction l E X m) (scalarReductionDerivedRestriction l E X n)
      (scalarReductionDerivedRestriction l L X m) (scalarReductionDerivedRestriction l L X n)
      (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m))
      (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n))
      (normalizedDVRRes l E X h) (normalizedDVRRes l L X h)
      (normalizedDVRResCompletedComp l E X D hl h)
      (normalizedDVRResCompletedComp l L X D hl h)
      (residualRestriction l E L ι X m) (residualRestriction l E L ι X n)
      (scalarRestrictionSquare l E L ι X h).hom := by
  let e₀ := Functor.isoWhiskerRight (eqToIso (scalarQuotient_restrict l E X h))
      (pbcDerivedRestrict (completedIntegralCommRingProjectionUnrestricted l E X m)) ≪≫
    pbcDerivedRestrictComp (completedIntegralCommRingProjectionUnrestricted l E X m)
      (scalarQuotient l E X h) (completedIntegralCommRingProjectionUnrestricted l E X n)
      (projection_quotient l E X h)
  let e₀' := Functor.isoWhiskerRight (eqToIso (scalarQuotient_restrict l L X h))
      (pbcDerivedRestrict (completedIntegralCommRingProjectionUnrestricted l L X m)) ≪≫
    pbcDerivedRestrictComp (completedIntegralCommRingProjectionUnrestricted l L X m)
      (scalarQuotient l L X h) (completedIntegralCommRingProjectionUnrestricted l L X n)
      (projection_quotient l L X h)
  let dm₀ := pbcDerivedRestrictComp
      (completedIntegralCommRingProjectionUnrestricted l E X m)
      (integralScalarQuotientSheafMap l E L ι X m)
      (completedCoefficientMap l E L ι X ≫
        completedIntegralCommRingProjectionUnrestricted l L X m)
      ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec m).symm ≪≫
    (pbcDerivedRestrictComp (completedCoefficientMap l E L ι X)
      (completedIntegralCommRingProjectionUnrestricted l L X m) _ rfl).symm
  let dn₀ := pbcDerivedRestrictComp
      (completedIntegralCommRingProjectionUnrestricted l E X n)
      (integralScalarQuotientSheafMap l E L ι X n)
      (completedCoefficientMap l E L ι X ≫
        completedIntegralCommRingProjectionUnrestricted l L X n)
      ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec n).symm ≪≫
    (pbcDerivedRestrictComp (completedCoefficientMap l E L ι X)
      (completedIntegralCommRingProjectionUnrestricted l L X n) _ rfl).symm
  have he : HEq (normalizedDVRResCompletedComp l E X D hl h) e₀ := by
    rw [completed_comp_eq]
    exact whiskerRight_comp_heq (scalarRestriction_eq l E X m)
      (scalarRestriction_eq l E X n) (eqToIso (scalarQuotient_restrict l E X h))
      _ _ (HEq.refl _)
  have he' : HEq (normalizedDVRResCompletedComp l L X D hl h) e₀' := by
    rw [completed_comp_eq]
    exact whiskerRight_comp_heq (scalarRestriction_eq l L X m)
      (scalarRestriction_eq l L X n) (eqToIso (scalarQuotient_restrict l L X h))
      _ _ (HEq.refl _)
  have ht := restriction_cube_transport (completedCoefficientMap l E L ι X)
      (completedIntegralCommRingProjectionUnrestricted l E X m) (scalarQuotient l E X h)
      (completedIntegralCommRingProjectionUnrestricted l E X n)
      (completedIntegralCommRingProjectionUnrestricted l L X m) (scalarQuotient l L X h)
      (completedIntegralCommRingProjectionUnrestricted l L X n)
      (integralScalarQuotientSheafMap l E L ι X m)
      (integralScalarQuotientSheafMap l E L ι X n)
      ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec m)
      ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec n)
      (projection_quotient l E X h) (projection_quotient l L X h)
      (scalarQuotient_square l E L ι X h)
      (normalizedDVRRes l E X h) (normalizedDVRRes l L X h)
      (scalarQuotient_restrict l E X h) (scalarQuotient_restrict l L X h)
  apply cube_transfer_heq
      (C := nativeDerived X (completedIntegralCommRingSheafUnrestricted l E X))
      (D := nativeDerived X (completedIntegralCommRingSheafUnrestricted l L X))
      (A := nativeDerived X (integralCoefficientCommRingSheaf l E X m))
      (B := nativeDerived X (integralCoefficientCommRingSheaf l E X n))
      (A' := nativeDerived X (integralCoefficientCommRingSheaf l L X m))
      (B' := nativeDerived X (integralCoefficientCommRingSheaf l L X n))
    (scalarRestriction_eq l E X m) (scalarRestriction_eq l E X n)
    (scalarRestriction_eq l L X m) (scalarRestriction_eq l L X n)
    (e₀ := e₀) (e₀' := e₀') (dm₀ := dm₀) (dn₀ := dn₀) he he'
    (by unfold residualRestriction; rfl)
    (by unfold residualRestriction; rfl)
  exact ht

end ResidualCube

/-- The residual composite before applying the outer normalized Hom equivalence.
Source: current blueprint residual mate calculation.
(blueprint: lem-sf-integral-scalar-quotient-residual-mate-transport)
-/
def residualTransportMap
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K)
    {m n : ℕ} (h : n ≤ m) :
    (scalarReductionDerivedExtension l L X m).obj
        ((integralScalarExtensionOfUniverses l E L ι X).obj K) ⟶
      ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n) ⋙
        normalizedDVRRes l L X h).obj ((scalarReductionDerivedExtension l E X n).obj K)) :=
  (scalarReductionDerivedExtension l L X m).map (completion l E L ι X K hK).inv ≫
    (quotientResidual l E L ι X K m).hom ≫
    (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
      (normalizedDVRReductionTransition l E X D hl h K) ≫
    (scalarReductionExchange l E L ι X h).app
      ((scalarReductionDerivedExtension l E X n).obj K)

attribute [local semireducible] normalizedDVRReductionTransition

private theorem reductionTransition_eq {m n : ℕ} (h : n ≤ m)
    (M : IntegralVerdier.Ambient l E X) :
    normalizedDVRReductionTransition l E X D hl h M =
      ((normalizedDVRIntegralAdjunction l E X m).homEquiv M _).symm
        ((normalizedDVRIntegralAdjunction l E X n).unit.app M ≫
          (normalizedDVRResCompletedComp l E X D hl h).inv.app
            ((scalarReductionDerivedExtension l E X n).obj M)) := by
  rfl

private theorem reductionTransition_unit {m n : ℕ} (h : n ≤ m)
    (M : IntegralVerdier.Ambient l E X) :
    (normalizedDVRIntegralAdjunction l E X m).homEquiv _ _
        (normalizedDVRReductionTransition l E X D hl h M) =
      (normalizedDVRIntegralAdjunction l E X n).unit.app M ≫
        (normalizedDVRResCompletedComp l E X D hl h).inv.app
          ((scalarReductionDerivedExtension l E X n).obj M) := by
  exact transition_unit_named
    (normalizedDVRIntegralAdjunction l E X m) (normalizedDVRIntegralAdjunction l E X n)
    (normalizedDVRRes l E X h) (normalizedDVRResCompletedComp l E X D hl h)
    M (normalizedDVRReductionTransition l E X D hl h M)
    (reductionTransition_eq l E X D hl h M)

attribute [local semireducible] scalarReductionExchange

private theorem scalarExchange_eq {m n : ℕ} (h : n ≤ m) :
    scalarReductionExchange l E L ι X h =
      ((mateEquiv
        (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n))
        (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X m))).symm
          (TwoSquare.mk _ _ _ _ (scalarRestrictionSquare l E L ι X h).hom)).natTrans := by
  rfl

private theorem scalarExchange_unit {m n : ℕ} (h : n ≤ m)
    (M : @DerivedCategory
      (pbcModules X (integralCoefficientCommRingSheaf l E X n)) _ _
      (proEtaleRingModules_hasDerivedCategory X
        (integralCoefficientCommRingSheaf l E X n))) :
    (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X m)).unit.app
        ((normalizedDVRRes l E X h).obj M) ≫
      (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m)).map
        ((scalarReductionExchange l E L ι X h).app M) =
      (normalizedDVRRes l E X h).map
          ((pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n)).unit.app M) ≫
        (scalarRestrictionSquare l E L ι X h).hom.app
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj M) := by
  exact mixed_unit_named
    (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n))
    (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X m))
    (normalizedDVRRes l E X h) (normalizedDVRRes l L X h)
    (scalarRestrictionSquare l E L ι X h).hom (scalarReductionExchange l E L ι X h)
    (scalarExchange_eq l E L ι X h) M

private theorem scalarExchange_reduction_unit (K : IntegralVerdier.Ambient l E X)
    {m n : ℕ} (h : n ≤ m) :
    (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X m)).unit.app
      ((normalizedDVRRes l E X h).obj ((scalarReductionDerivedExtension l E X n).obj K)) ≫
      (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m)).map
        ((scalarReductionExchange l E L ι X h).app
          ((scalarReductionDerivedExtension l E X n).obj K)) =
      (normalizedDVRRes l E X h).map
        ((pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n)).unit.app
          ((scalarReductionDerivedExtension l E X n).obj K)) ≫
        (scalarRestrictionSquare l E L ι X h).hom.app
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
            ((scalarReductionDerivedExtension l E X n).obj K)) := by
  exact scalarExchange_unit l E L ι X h _

private theorem residualFiniteTranspose
    (K : IntegralVerdier.Ambient l E X) {m n : ℕ} (h : n ≤ m) :
    (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X m)).homEquiv _ _
      ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
      (normalizedDVRReductionTransition l E X D hl h K) ≫ (scalarReductionExchange l E L ι X h).app
      ((scalarReductionDerivedExtension l E X n).obj K)) =
      (normalizedDVRReductionTransition l E X D hl h K) ≫ (normalizedDVRRes l E X h).map
        ((pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n)).unit.app
        ((scalarReductionDerivedExtension l E X n).obj K)) ≫ (scalarRestrictionSquare l E L ι X
        h).hom.app ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
        ((scalarReductionDerivedExtension l E X n).obj K)) := by
    erw [(pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X
      m)).homEquiv_naturality_left, Adjunction.homEquiv_unit, (scalarExchange_reduction_unit l E L ι
      X K h)]

private theorem residualPostcompose (K : IntegralVerdier.Ambient l E X) (j : ℕ)
    {N : @DerivedCategory (pbcModules X (integralCoefficientCommRingSheaf l L X j)) _ _
      (proEtaleRingModules_hasDerivedCategory X (integralCoefficientCommRingSheaf l L X j))}
    (f : (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X j)).obj
      ((scalarReductionDerivedExtension l E X j).obj K) ⟶ N) :
    (pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X)).homEquiv _ _
      ((normalizedDVRIntegralAdjunction l L X j).homEquiv _ _
        ((quotientResidual l E L ι X K j).hom ≫ f)) =
      (normalizedDVRIntegralAdjunction l E X j).unit.app K ≫
        (scalarReductionDerivedRestriction l E X j).map
          ((pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X j)).homEquiv
            _ _ f) ≫ (residualRestriction l E L ι X j).hom.app N := by
  exact comparison_postcompose
    (pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X))
    (normalizedDVRIntegralAdjunction l E X j) (normalizedDVRIntegralAdjunction l L X j)
    (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X j))
    (residualRestriction l E L ι X j) K (quotientResidual l E L ι X K j).hom
    (quotientResidual_unit l E L ι X K j) f

private theorem residualRestrictionCalculation
    (K : IntegralVerdier.Ambient l E X) {m n : ℕ} (h : n ≤ m) :
    (normalizedDVRIntegralAdjunction l E X m).unit.app K ≫
      (scalarReductionDerivedRestriction l E X m).map
        (normalizedDVRReductionTransition l E X D hl h K ≫
          (normalizedDVRRes l E X h).map
            ((pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n)).unit.app
              ((scalarReductionDerivedExtension l E X n).obj K)) ≫
          (scalarRestrictionSquare l E L ι X h).hom.app
            ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
              ((scalarReductionDerivedExtension l E X n).obj K))) ≫
      (residualRestriction l E L ι X m).hom.app
        ((normalizedDVRRes l L X h).obj
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
            ((scalarReductionDerivedExtension l E X n).obj K))) =
    (pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X)).homEquiv _ _
      ((normalizedDVRIntegralAdjunction l L X n).homEquiv _ _
        (quotientResidual l E L ι X K n).hom) ≫
      (pbcDerivedRestrict (completedCoefficientMap l E L ι X)).map
        ((normalizedDVRResCompletedComp l L X D hl h).inv.app
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
            ((scalarReductionDerivedExtension l E X n).obj K))) := by
  have hs := restriction_transition_calculation
    (pbcDerivedRestrict (completedCoefficientMap l E L ι X))
    (scalarReductionDerivedRestriction l E X m) (scalarReductionDerivedRestriction l E X n)
    (scalarReductionDerivedRestriction l L X m) (scalarReductionDerivedRestriction l L X n)
    (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m))
    (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n))
    (normalizedDVRRes l E X h) (normalizedDVRRes l L X h)
    (normalizedDVRResCompletedComp l E X D hl h)
    (normalizedDVRResCompletedComp l L X D hl h)
    (residualRestriction l E L ι X m) (residualRestriction l E L ι X n)
    (scalarRestrictionSquare l E L ι X h).hom
    (residualRestriction_cube l E L ι X D hl h)
    ((normalizedDVRIntegralAdjunction l E X m).unit.app K)
    ((normalizedDVRIntegralAdjunction l E X n).unit.app K)
    (normalizedDVRReductionTransition l E X D hl h K)
    ((pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n)).unit.app
      ((scalarReductionDerivedExtension l E X n).obj K))
    (by simpa only [Adjunction.homEquiv_unit] using reductionTransition_unit l E X D hl h K)
  erw [← reassoc_of% (quotientResidual_unit l E L ι X K n)] at hs
  exact hs

private theorem residualLeftTranspose
    (K : IntegralVerdier.Ambient l E X) {m n : ℕ} (h : n ≤ m) :
    (pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X)).homEquiv _ _
      ((normalizedDVRIntegralAdjunction l L X m).homEquiv _ _ ((quotientResidual l E L ι X K m).hom
      ≫
      (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
        (normalizedDVRReductionTransition l E X D hl h K) ≫
      (scalarReductionExchange l E L ι X h).app
        ((scalarReductionDerivedExtension l E X n).obj K))) =
    (pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X)).homEquiv _ _
      ((normalizedDVRIntegralAdjunction l L X n).homEquiv _ _ (quotientResidual l E L ι X K n).hom)
      ≫
      (pbcDerivedRestrict (completedCoefficientMap l E L ι X)).map
        ((normalizedDVRResCompletedComp l L X D hl h).inv.app
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
            ((scalarReductionDerivedExtension l E X n).obj K))) := by
  have hf := residualFiniteTranspose l E L ι X D hl K h
  have hp := residualPostcompose l E L ι X K m
    ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
        (normalizedDVRReductionTransition l E X D hl h K) ≫
      (scalarReductionExchange l E L ι X h).app
        ((scalarReductionDerivedExtension l E X n).obj K))
  have hm := congrArg (fun f ↦
    (normalizedDVRIntegralAdjunction l E X m).unit.app K ≫
      (scalarReductionDerivedRestriction l E X m).map f ≫
        (residualRestriction l E L ι X m).hom.app
          ((normalizedDVRRes l L X h).obj
            ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
              ((scalarReductionDerivedExtension l E X n).obj K)))) hf
  exact hp.trans (hm.trans (residualRestrictionCalculation l E L ι X D hl K h))

private theorem residualRightTranspose
    (K : IntegralVerdier.Ambient l E X) {m n : ℕ} (h : n ≤ m) :
    (pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X)).homEquiv _ _
      ((normalizedDVRIntegralAdjunction l L X m).homEquiv _ _ (normalizedDVRReductionTransition l L
      X D hl h
        ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K) ≫
      (normalizedDVRRes l L X h).map (quotientResidual l E L ι X K n).hom)) =
    (pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X)).homEquiv _ _
      ((normalizedDVRIntegralAdjunction l L X n).homEquiv _ _ (quotientResidual l E L ι X K n).hom)
      ≫
      (pbcDerivedRestrict (completedCoefficientMap l E L ι X)).map
        ((normalizedDVRResCompletedComp l L X D hl h).inv.app
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
            ((scalarReductionDerivedExtension l E X n).obj K))) := by
  symm
  erw [(normalizedDVRIntegralAdjunction l L X m).homEquiv_naturality_right,
    (reductionTransition_unit l L X D hl h _)]
  have he' := (normalizedDVRResCompletedComp l L X D hl h).inv.naturality (quotientResidual l E L ι
    X K n).hom
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at he'
  simp only [Category.assoc]
  erw [← he']
  conv_rhs => erw [← Category.assoc, ← (normalizedDVRIntegralAdjunction l L X n).homEquiv_unit]
  erw [(pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X)).homEquiv_naturality_right]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private theorem quotientResidual_square
    (K : IntegralVerdier.Ambient l E X) {m n : ℕ} (h : n ≤ m) :
    (quotientResidual l E L ι X K m).hom ≫
      (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
        (normalizedDVRReductionTransition l E X D hl h K) ≫
      (scalarReductionExchange l E L ι X h).app
        ((scalarReductionDerivedExtension l E X n).obj K) =
    normalizedDVRReductionTransition l L X D hl h
        ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K) ≫
      (normalizedDVRRes l L X h).map (quotientResidual l E L ι X K n).hom := by
  apply ((normalizedDVRIntegralAdjunction l L X m).homEquiv _ _).injective
  apply ((pbcDerivedScalarAdjunction (completedCoefficientMap l E L ι X)).homEquiv _ _).injective
  exact (residualLeftTranspose l E L ι X D hl K h).trans
    (residualRightTranspose l E L ι X D hl K h).symm

/-- Lower residual mate transport statement used by the core transpose theorem.

Source: current blueprint, lem-sf-integral-scalar-quotient-transition, proof step 2.
(blueprint: lem-sf-integral-scalar-quotient-residual-mate-transport)
-/
theorem residual_mate_transport
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K)
    {m n : ℕ} (h : n ≤ m) :
    (normalizedDVRIntegralAdjunction l L X m).homEquiv
          ((integralScalarExtensionOfUniverses l E L ι X).obj K)
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n) ⋙
            normalizedDVRRes l L X h).obj ((scalarReductionDerivedExtension l E X n).obj K))
          (residualTransportMap l E L ι X D hl K hK h) =
      (normalizedDVRIntegralAdjunction l L X n).unit.app
          ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≫
        (normalizedDVRIntegralAdjunction l L X m).homEquiv
          ((scalarReductionDerivedExtension l L X n ⋙
            scalarReductionDerivedRestriction l L X n).obj
              ((integralScalarExtensionOfUniverses l E L ι X).obj K))
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n) ⋙
            normalizedDVRRes l L X h).obj ((scalarReductionDerivedExtension l E X n).obj K))
          ((scalarReductionDerivedExtension l L X m).map
              ((normalizedDVRResCompletedComp l L X D hl h).inv.app
                ((scalarReductionDerivedExtension l L X n).obj
                  ((integralScalarExtensionOfUniverses l E L ι X).obj K))) ≫
            (normalizedDVRIntegralAdjunction l L X m).counit.app
              ((normalizedDVRRes l L X h).obj
                ((scalarReductionDerivedExtension l L X n).obj
                  ((integralScalarExtensionOfUniverses l E L ι X).obj K))) ≫
            (normalizedDVRRes l L X h).map
              ((scalarReductionDerivedExtension l L X n).map (completion l E L ι X K hK).inv ≫
                (quotientResidual l E L ι X K n).hom)) := by
  rw [residualTransportMap.eq_1]
  refine transported_transpose_named
    (normalizedDVRIntegralAdjunction l L X m) (normalizedDVRIntegralAdjunction l L X n)
    (normalizedDVRRes l L X h) (normalizedDVRResCompletedComp l L X D hl h)
    (completion l E L ι X K hK).inv _
    (quotientResidual l E L ι X K n).hom
    (normalizedDVRReductionTransition l L X D hl h
      ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K))
    (reductionTransition_eq l L X D hl h _) ?_
  -- Abstract the exchange transformation: otherwise the kernel unfolds `NatTrans.app` of it
  -- when the two composites differ only in how their implicit categories are presented.
  have q := quotientResidual_square l E L ι X D hl K h
  obtain ⟨ex, hex⟩ : ∃ ex, scalarReductionExchange l E L ι X h = ex := ⟨_, rfl⟩
  rw [hex] at q ⊢
  exact q

/-- The residual transpose identity used by the scalar quotient transition theorem.

Source: current blueprint, lem-sf-integral-scalar-quotient-transition, proof step 2.
(blueprint: lem-sf-integral-scalar-quotient-transition-transpose-core)
-/
theorem quotient_reduction_transition_transpose_core
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K)
    {m n : ℕ} (h : n ≤ m) :
    (completion l E L ι X K hK).inv ≫
        (normalizedDVRIntegralAdjunction l L X m).homEquiv
          ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K)
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n) ⋙
            normalizedDVRRes l L X h).obj ((scalarReductionDerivedExtension l E X n).obj K))
          ((quotientResidual l E L ι X K m).hom ≫
            (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
              (normalizedDVRReductionTransition l E X D hl h K) ≫
            (scalarReductionExchange l E L ι X h).app
              ((scalarReductionDerivedExtension l E X n).obj K)) =
      (normalizedDVRIntegralAdjunction l L X n).unit.app
          ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≫
        (normalizedDVRIntegralAdjunction l L X m).homEquiv
          ((scalarReductionDerivedExtension l L X n ⋙
            scalarReductionDerivedRestriction l L X n).obj
              ((integralScalarExtensionOfUniverses l E L ι X).obj K))
          ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n) ⋙
            normalizedDVRRes l L X h).obj ((scalarReductionDerivedExtension l E X n).obj K))
          ((scalarReductionDerivedExtension l L X m).map
              ((normalizedDVRResCompletedComp l L X D hl h).inv.app
                ((scalarReductionDerivedExtension l L X n).obj
                  ((integralScalarExtensionOfUniverses l E L ι X).obj K))) ≫
            (normalizedDVRIntegralAdjunction l L X m).counit.app
              ((normalizedDVRRes l L X h).obj
                ((scalarReductionDerivedExtension l L X n).obj
                  ((integralScalarExtensionOfUniverses l E L ι X).obj K))) ≫
            (normalizedDVRRes l L X h).map
              ((scalarReductionDerivedExtension l L X n).map (completion l E L ι X K hK).inv ≫
                (quotientResidual l E L ι X K n).hom)) := by
  rw [← Category.assoc]
  rw [← (normalizedDVRIntegralAdjunction l L X m).homEquiv_naturality_left]
  have q := residual_mate_transport l E L ι X D hl K hK h
  rw [residualTransportMap.eq_1] at q
  -- As above, keep the exchange transformation opaque for the kernel.
  obtain ⟨ex, hex⟩ : ∃ ex, scalarReductionExchange l E L ι X h = ex := ⟨_, rfl⟩
  rw [hex] at q ⊢
  simpa only [Category.assoc] using q

end WeilConjectures.IntegralFiniteExtension
