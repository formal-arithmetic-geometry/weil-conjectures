/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module

public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Tactic.DSimpPercent
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Coherence from section-normalized ordinary pullback comparisons
Source: Stacks 0D6D and the site pullback associativity law.
(blueprint: lem-pur-normalized-derived-pullback-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u

open scoped AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] CategoryTheory.constantSheaf conjugateIsoEquiv
  proEtaleRingModuleAdjunction conjugateEquiv proEtaleRingDirectImageMap
  proEtaleConstantRingComparison proEtaleRingModulePullback
  proEtaleRingModulePullbackObj proEtaleRingModulePullbackMap
  Functor.mapDerivedCategory

set_option linter.auxLemma false
attribute [local instance 10000] HasDerivedCategory.standard
  proEtaleDerivedCategory._proof_3 proEtaleDerivedCategory._proof_4

/-- The category instance in the definition of the intrinsic derived category. -/
abbrev proEtaleDerivedCanonicalCategory (T : Scheme.{u})
    (A : Type u) [CommRing A] : Category (proEtaleDerivedCategory T A) :=
  dsimp% only [inferInstance] (inferInstance : Category (proEtaleDerivedCategory T A))

variable (A : Type u) [CommRing A]
variable (comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
  proEtaleConstantRingPullback A (f ≫ g) ≅
    proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (hc : ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
  (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
  (m : ((proEtaleConstantRingPushforward A f ⋙
    proEtaleConstantRingPushforward A g).obj M).val.obj (Opposite.op V)),
  ((conjugateIsoEquiv
    ((proEtaleConstantRingAdjunction A g).comp (proEtaleConstantRingAdjunction A f))
    (proEtaleConstantRingAdjunction A (f ≫ g)) (comp f g)).hom.app M).val.app
      (Opposite.op V) m =
    M.val.map ((MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) f g).hom.app V).op m)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

@[irreducible] private noncomputable def normalizedAdj
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f :=
  proEtaleConstantRingAdjunction A f

@[irreducible] private noncomputable def directComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingPushforward A f ⋙ proEtaleConstantRingPushforward A g ≅
      proEtaleConstantRingPushforward A (f ≫ g) :=
  conjugateIsoEquiv ((normalizedAdj A g).comp (normalizedAdj A f))
    (normalizedAdj A (f ≫ g)) (comp f g)

private theorem mate_roundtrip
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    {R : D ⥤ C} {S : E ⥤ D} {T : E ⥤ C}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ T) (e : H ≅ F ⋙ G) :
    e = (Adjunction.leftAdjointCompIso a b c
      (conjugateIsoEquiv (a.comp b) c e)).symm := by
  apply Iso.ext
  apply (conjugateEquiv (a.comp b) c).injective
  simpa only [conjugateIsoEquiv_apply_hom, Iso.symm_hom] using
    (Adjunction.conjugateEquiv_leftAdjointCompIso_inv a b c
      (conjugateIsoEquiv (a.comp b) c e)).symm

private theorem ordinaryComp_eq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    comp f g =
      (Adjunction.leftAdjointCompIso (normalizedAdj A g) (normalizedAdj A f)
        (normalizedAdj A (f ≫ g)) (directComp A comp f g)).symm := by
  unfold directComp
  exact mate_roundtrip (normalizedAdj A g) (normalizedAdj A f)
    (normalizedAdj A (f ≫ g)) (comp f g)

private theorem directImage_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (N : proEtaleRingModules X (proEtaleConstantRing X A)) (U : Y.ProEt)
    (m : ((proEtaleConstantRingPushforward A f).obj N).val.obj (Opposite.op U)) :
    ((eqToIso (congrArg (proEtaleConstantRingPushforward A) e)).hom.app N).val.app
        (Opposite.op U) m =
      N.val.map (eqToHom (congrArg (fun t ↦ (proEtaleBaseChange t).obj U) e.symm)).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

private theorem pasting_transport
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (e : fg = f ≫ g) (U : P.Over Q Z) :
    (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g fg e).hom.app U =
      eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U) e) ≫
        (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g).hom.app U := by
  cases e
  simp

private theorem site_pasting
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y Z W : C} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X) (U : P.Over Q X) :
    (MorphismProperty.Over.pullbackComp j (h ≫ k)).hom.app U ≫
        (MorphismProperty.Over.pullback P Q j).map
          ((MorphismProperty.Over.pullbackComp h k).hom.app U) =
      eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U)
        (Category.assoc j h k).symm) ≫
        (MorphismProperty.Over.pullbackComp (j ≫ h) k).hom.app U ≫
        (MorphismProperty.Over.pullbackComp j h).hom.app
          ((MorphismProperty.Over.pullback P Q k).obj U) := by
  have hp := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_assoc (P := P) (Q := Q) j h k)) U
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hp
  rw [pasting_transport (j ≫ h) k (j ≫ h ≫ k) (Category.assoc j h k).symm U] at hp
  simpa only [Category.assoc] using hp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hc in
private theorem directComp_hom_apply
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (N : proEtaleRingModules Z (proEtaleConstantRing Z A)) (U : V.ProEt)
    (m : ((proEtaleConstantRingPushforward A h ⋙
      proEtaleConstantRingPushforward A k).obj N).val.obj (Opposite.op U)) :
    ((directComp A comp h k).hom.app N).val.app (Opposite.op U) m =
      N.val.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U).op m := by
  unfold directComp normalizedAdj
  exact hc _ _ _ h k N U m

private theorem directImage_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N N' : proEtaleRingModules X (proEtaleConstantRing X A)} (a : N ⟶ N') (U : Y.ProEt)
    (m : ((proEtaleConstantRingPushforward A f).obj N).val.obj (Opposite.op U)) :
    (((proEtaleConstantRingPushforward A f).map a).val.app (Opposite.op U)) m =
      a.val.app (Opposite.op ((proEtaleBaseChange f).obj U)) m := rfl

private theorem directImage_obj_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : proEtaleRingModules X (proEtaleConstantRing X A))
    {U V : Y.ProEt} (a : U ⟶ V)
    (m : ((proEtaleConstantRingPushforward A f).obj N).val.obj (Opposite.op V)) :
    (((proEtaleConstantRingPushforward A f).obj N).val.map a.op) m =
      N.val.map ((proEtaleBaseChange f).map a).op m := rfl

private theorem restriction_pasting
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat} (N : PresheafOfModules R)
    {U V T U' V' : C} (a : U ⟶ V) (b : V ⟶ T)
    (c : U ⟶ U') (d : U' ⟶ V') (e : V' ⟶ T)
    (h : a ≫ b = c ≫ d ≫ e) (m : N.obj (Opposite.op T)) :
    N.map a.op (N.map b.op m) = N.map c.op (N.map d.op (N.map e.op m)) := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp]
  rw [h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hc in
private theorem directImage_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    :
    Functor.isoWhiskerLeft (proEtaleConstantRingPushforward A j) (directComp A comp h k) ≪≫
        (directComp A comp j (h ≫ k)) =
      (Functor.associator (proEtaleConstantRingPushforward A j)
          (proEtaleConstantRingPushforward A h)
          (proEtaleConstantRingPushforward A k)).symm ≪≫
        Functor.isoWhiskerRight (directComp A comp j h)
          (proEtaleConstantRingPushforward A k) ≪≫
        (directComp A comp (j ≫ h) k) ≪≫
        eqToIso (congrArg (proEtaleConstantRingPushforward A) (Category.assoc j h k)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  ext m
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [directImage_map_apply A k ((directComp A comp j h).hom.app N) U]
  erw [directComp_hom_apply A comp hc j h N ((proEtaleBaseChange k).obj U)]
  erw [directComp_hom_apply A comp hc (j ≫ h) k N U]
  conv_rhs => erw [directImage_transport A (Category.assoc j h k) N U]
  conv_lhs => erw [directComp_hom_apply A comp hc h k
    ((proEtaleConstantRingPushforward A j).obj N) U m]
  conv_lhs => erw [directComp_hom_apply A comp hc j (h ≫ k) N U]
  conv_lhs => erw [directImage_obj_map_apply A j N
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U)]
  exact restriction_pasting N.val _ _ _ _ _
    (site_pasting (P := @WeaklyEtale) (Q := ⊤) j h k U) m

private theorem mate_transport
    {C D E I : Type*} [Category C] [Category D] [Category E]
    (L : I → C ⥤ E) (R : I → E ⥤ C) (adj : ∀ i, L i ⊣ R i)
    {F : C ⥤ D} {G : D ⥤ E} {F' : D ⥤ C} {G' : E ⥤ D}
    (aF : F ⊣ F') (aG : G ⊣ G') {i i' : I} (e : i = i')
    (d : G' ⋙ F' ≅ R i) :
    Adjunction.leftAdjointCompIso aF aG (adj i')
        (d ≪≫ eqToIso (congrArg R e)) =
      Adjunction.leftAdjointCompIso aF aG (adj i) d ≪≫ eqToIso (congrArg L e) := by
  cases e
  simp

include hc in
private theorem ordinary_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (comp j (h ≫ k)).hom.app M ≫
        (proEtaleConstantRingPullback A j).map ((comp h k).hom.app M) =
      (eqToIso (congrArg (proEtaleConstantRingPullback A)
        (Category.assoc j h k).symm)).hom.app M ≫
        (comp (j ≫ h) k).hom.app M ≫
        (comp j h).hom.app ((proEtaleConstantRingPullback A k).obj M) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (normalizedAdj A k) (normalizedAdj A h) (normalizedAdj A j)
    (normalizedAdj A (h ≫ k)) (normalizedAdj A (j ≫ h))
    (normalizedAdj A (j ≫ h ≫ k))
    (directComp A comp h k) (directComp A comp j h)
    ((directComp A comp (j ≫ h) k) ≪≫
      eqToIso (congrArg (proEtaleConstantRingPushforward A) (Category.assoc j h k)))
    (directComp A comp j (h ≫ k)) (directImage_coherence A comp hc j h k)
  have ht := mate_transport (proEtaleConstantRingPullback A)
    (proEtaleConstantRingPushforward A) (fun f ↦ normalizedAdj A f)
    (normalizedAdj A k) (normalizedAdj A (j ≫ h)) (Category.assoc j h k)
    (directComp A comp (j ≫ h) k)
  rw [ht] at hh
  have hi := NatTrans.congr_app (congrArg Iso.inv hh) M
  simpa only [ordinaryComp_eq, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id, Category.assoc, eqToIso.inv, eqToIso.hom]
    using hi.symm

private theorem descend_coherence
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B)
    (F02 : C ⥤ E) (F13 : D ⥤ B) (F03 F03' : C ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [F02.Additive] [F13.Additive]
    [F03.Additive] [F03'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F02] [PreservesFiniteColimits F02]
    [PreservesFiniteLimits F13] [PreservesFiniteColimits F13]
    [PreservesFiniteLimits F03] [PreservesFiniteColimits F03]
    [PreservesFiniteLimits F03'] [PreservesFiniteColimits F03']
    (a02 : F02 ≅ F ⋙ G) (a13 : F13 ≅ G ⋙ H)
    (a0 : F03 ≅ F02 ⋙ H) (a1 : F03' ≅ F ⋙ F13) (e : F03 ≅ F03')
    (ho : a0 ≪≫ Functor.isoWhiskerRight a02 H =
      e ≪≫ a1 ≪≫ Functor.isoWhiskerLeft F a13) :
    (Functor.mapDerivedCategoryNatIso a0).hom ≫
        (Functor.mapDerivedCategoryCompIso F02 H).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso a02).hom
          H.mapDerivedCategory ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompIso F G).hom
          H.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso e).hom ≫
        (Functor.mapDerivedCategoryNatIso a1).hom ≫
        (Functor.mapDerivedCategoryCompIso F F13).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryNatIso a13).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryCompIso G H).hom := by
  have hd := congrArg (fun t ↦ (Functor.mapDerivedCategoryNatIso t).hom) ho
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hd
  have hR := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a02 H
  have hL := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F a13
  have hC := Functor.mapDerivedCategoryCompIso_assoc F G H
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F02 H).hom,
    ← hR, Category.assoc, ← hC]
  have ht := congrArg (fun t ↦ t ≫
    (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).hom ≫
    Functor.whiskerLeft F.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso G H).hom) hd
  calc
    _ = ((Functor.mapDerivedCategoryNatIso e).hom ≫
          (Functor.mapDerivedCategoryNatIso a1).hom ≫
          (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F a13)).hom) ≫
        (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso G H).hom := by
            simpa only [Category.assoc] using ht
    _ = _ := by
      simp only [Category.assoc]
      rw [← Category.assoc (Functor.mapDerivedCategoryNatIso
        (Functor.isoWhiskerLeft F a13)).hom, hL]
      simp only [Category.assoc]



private theorem derived_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    ((Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
      (C := proEtaleRingModules Y (proEtaleConstantRing Y A))
      (D := proEtaleRingModules X (proEtaleConstantRing X A))
      (F := proEtaleConstantRingPullback A f)
      (G := proEtaleConstantRingPullback A g)
      (eqToIso (congrArg (proEtaleConstantRingPullback A) e))) :
      proEtaleConstantRingDerivedPullback A f ≅
        proEtaleConstantRingDerivedPullback A g).hom =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl


include hc in
/-- Section-normalized ordinary pro-etale pullback comparisons have associative exact
 derived descents. Source: Stacks 0D6D, via site pasting and adjunction mates.
 (blueprint: lem-pur-normalized-derived-pullback-coherence). -/
theorem proEtaleNormalizedDerivedComp_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (M : proEtaleDerivedCategory X A) :
    (proEtaleFrobeniusDerivedComp A j (h ≫ k) (comp j (h ≫ k))).hom.app M ≫
        (proEtaleConstantRingDerivedPullback A j).map
          ((proEtaleFrobeniusDerivedComp A h k (comp h k)).hom.app M) =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
        (Category.assoc j h k).symm)).hom.app M ≫
        (proEtaleFrobeniusDerivedComp A (j ≫ h) k (comp (j ≫ h) k)).hom.app M ≫
        (proEtaleFrobeniusDerivedComp A j h (comp j h)).hom.app
          ((proEtaleConstantRingDerivedPullback A k).obj M) := by
  let F := proEtaleConstantRingPullback A k
  let G := proEtaleConstantRingPullback A h
  let H := proEtaleConstantRingPullback A j
  let F02 := proEtaleConstantRingPullback A (h ≫ k)
  let F13 := proEtaleConstantRingPullback A (j ≫ h)
  let a02 := comp h k
  let a13 := comp j h
  let a0 := comp j (h ≫ k)
  let a1 := comp (j ≫ h) k
  let e := eqToIso (congrArg (proEtaleConstantRingPullback A)
    (Category.assoc j h k).symm)
  have ho : a0 ≪≫ Functor.isoWhiskerRight a02 H =
      e ≪≫ a1 ≪≫ Functor.isoWhiskerLeft F a13 := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    exact ordinary_coherence A comp hc j h k N
  have hh := descend_coherence F G H F02 F13
    (proEtaleConstantRingPullback A (j ≫ h ≫ k))
    (proEtaleConstantRingPullback A ((j ≫ h) ≫ k)) a02 a13 a0 a1 e ho
  have hm := NatTrans.congr_app hh M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hm
  have he := NatTrans.congr_app
    (derived_transport A (Category.assoc j h k).symm) M
  change (Functor.mapDerivedCategoryNatIso e).hom.app M = _ at he
  rw [he] at hm
  simpa only [proEtaleDerivedCanonicalCategory,
    proEtaleConstantRingDerivedPullback, proEtaleFrobeniusDerivedComp,
    Iso.trans_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] using hm


end AlgebraicGeometry.Scheme
