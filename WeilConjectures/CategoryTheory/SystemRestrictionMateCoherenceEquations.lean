/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SystemEvaluationNormalizationData
import WeilConjectures.CategoryTheory.DerivedExactCube
import WeilConjectures.CategoryTheory.ExchangeMateCube
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Restriction mates and their coherence

Source: Stacks Project, Tags 03D2, 0D6E and 07A6; Zheng, Construction 4.1.
(blueprint: lem-route-system-restriction-mate-coherence-equations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem restriction_mate_transition
    {A B An Bn Am Bm : Type*}
    [Category A] [Category B] [Category An] [Category Bn] [Category Am] [Category Bm]
    {L : A ⥤ B} {R : B ⥤ A} {Ln : An ⥤ Bn} {Rn : Bn ⥤ An}
    {Lm : Am ⥤ Bm} {Rm : Bm ⥤ Am}
    (adj : L ⊣ R) (adjn : Ln ⊣ Rn) (adjm : Lm ⊣ Rm)
    {Un : A ⥤ An} {Vn : B ⥤ Bn} {Um : A ⥤ Am} {Vm : B ⥤ Bm}
    {qA : An ⥤ Am} {qB : Bn ⥤ Bm}
    (cn : L ⋙ Vn ≅ Un ⋙ Ln) (cm : L ⋙ Vm ≅ Um ⋙ Lm)
    (s : Ln ⋙ qB ≅ qA ⋙ Lm)
    (tA : Um ⟶ Un ⋙ qA) (tB : Vm ⟶ Vn ⋙ qB)
    (ht : ∀ X : A,
      tB.app (L.obj X) ≫ qB.map (cn.hom.app X) ≫ s.hom.app (Un.obj X) =
        cm.hom.app X ≫ Lm.map (tA.app X)) (Z : B) :
    tA.app (R.obj Z) ≫
        qA.map ((mateEquiv adj adjn (TwoSquare.mk _ _ _ _ cn.inv)).app Z) ≫
        (mateEquiv adjn adjm (TwoSquare.mk _ _ _ _ s.inv)).app (Vn.obj Z) =
      (mateEquiv adj adjm (TwoSquare.mk _ _ _ _ cm.inv)).app Z ≫
        Rm.map (tB.app Z) := by
  let bn := (mateEquiv adj adjn (TwoSquare.mk _ _ _ _ cn.inv)).natTrans
  let bm := (mateEquiv adj adjm (TwoSquare.mk _ _ _ _ cm.inv)).natTrans
  let th := (mateEquiv adjn adjm (TwoSquare.mk _ _ _ _ s.inv)).natTrans
  have hn := mateEquiv_counit adj adjn (TwoSquare.mk _ _ _ _ cn.inv) Z
  have hm := mateEquiv_counit adj adjm (TwoSquare.mk _ _ _ _ cm.inv) Z
  have hs := mateEquiv_counit adjn adjm (TwoSquare.mk _ _ _ _ s.inv) (Vn.obj Z)
  change Ln.map (bn.app Z) ≫ adjn.counit.app (Vn.obj Z) =
    cn.inv.app (R.obj Z) ≫ Vn.map (adj.counit.app Z) at hn
  change Lm.map (bm.app Z) ≫ adjm.counit.app (Vm.obj Z) =
    cm.inv.app (R.obj Z) ≫ Vm.map (adj.counit.app Z) at hm
  change Lm.map (th.app (Vn.obj Z)) ≫ adjm.counit.app (qB.obj (Vn.obj Z)) =
    s.inv.app (Rn.obj (Vn.obj Z)) ≫ qB.map (adjn.counit.app (Vn.obj Z)) at hs
  change tA.app (R.obj Z) ≫ qA.map (bn.app Z) ≫ th.app (Vn.obj Z) =
    bm.app Z ≫ Rm.map (tB.app Z)
  apply (adjm.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hs]
  have sn := s.inv.naturality (bn.app Z)
  dsimp only [Functor.comp_map, Functor.comp_obj] at sn
  rw [← Category.assoc (Lm.map (qA.map (bn.app Z))), sn]
  simp only [Category.assoc, ← qB.map_comp, hn]
  simp only [Functor.map_comp]
  have hh : Lm.map (tA.app (R.obj Z)) ≫ s.inv.app (Un.obj (R.obj Z)) ≫
      qB.map (cn.inv.app (R.obj Z)) =
      cm.inv.app (R.obj Z) ≫ tB.app (L.obj (R.obj Z)) := by
    apply (cancel_epi (cm.hom.app (R.obj Z))).1
    rw [← Category.assoc, ← ht]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
      ← Functor.map_comp]
    erw [qB.map_id, Category.comp_id]
  rw [reassoc_of% hh]
  have tn := tB.naturality (adj.counit.app Z)
  dsimp only [Functor.comp_map, Functor.comp_obj] at tn
  rw [← tn]
  have en := adjm.counit.naturality (tB.app Z)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at en
  rw [en, reassoc_of% hm]
  simp only [Functor.id_obj]



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 500000 in
-- The factorization calculation traverses nine exact-functor localizations.
private theorem localized_transition_square
    {A B An Bn Am Bm : Type*}
    [Category A] [Category B] [Category An] [Category Bn] [Category Am] [Category Bm]
    [Abelian A] [Abelian B] [Abelian An] [Abelian Bn] [Abelian Am] [Abelian Bm]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory An] [HasDerivedCategory Bn]
    [HasDerivedCategory Am] [HasDerivedCategory Bm]
    (L : A ⥤ B) (Ln : An ⥤ Bn) (Lm : Am ⥤ Bm)
    (Un : A ⥤ An) (Vn : B ⥤ Bn) (Um : A ⥤ Am) (Vm : B ⥤ Bm)
    (qA : An ⥤ Am) (qB : Bn ⥤ Bm)
    [L.Additive] [Ln.Additive] [Lm.Additive] [Un.Additive] [Vn.Additive]
    [Um.Additive] [Vm.Additive] [qA.Additive] [qB.Additive]
    [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    [Limits.PreservesFiniteLimits Ln] [Limits.PreservesFiniteColimits Ln]
    [Limits.PreservesFiniteLimits Lm] [Limits.PreservesFiniteColimits Lm]
    [Limits.PreservesFiniteLimits Un] [Limits.PreservesFiniteColimits Un]
    [Limits.PreservesFiniteLimits Vn] [Limits.PreservesFiniteColimits Vn]
    [Limits.PreservesFiniteLimits Um] [Limits.PreservesFiniteColimits Um]
    [Limits.PreservesFiniteLimits Vm] [Limits.PreservesFiniteColimits Vm]
    [Limits.PreservesFiniteLimits qA] [Limits.PreservesFiniteColimits qA]
    [Limits.PreservesFiniteLimits qB] [Limits.PreservesFiniteColimits qB]
    (cn : L ⋙ Vn ≅ Un ⋙ Ln) (cm : L ⋙ Vm ≅ Um ⋙ Lm)
    (s : Ln ⋙ qB ≅ qA ⋙ Lm)
    (tA : Um ⟶ Un ⋙ qA) (tB : Vm ⟶ Vn ⋙ qB)
    (tdA : Um.mapDerivedCategory ⟶ Un.mapDerivedCategory ⋙ qA.mapDerivedCategory)
    (tdB : Vm.mapDerivedCategory ⟶ Vn.mapDerivedCategory ⋙ qB.mapDerivedCategory)
    (htA : ∀ X : CochainComplex A ℤ,
      tdA.app (DerivedCategory.Q.obj X) ≫
        qA.mapDerivedCategory.map (Un.mapDerivedCategoryFactors.hom.app X) ≫
        qA.mapDerivedCategoryFactors.hom.app ((Un.mapHomologicalComplex (.up ℤ)).obj X) =
      Um.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex tA (.up ℤ)).app X))
    (htB : ∀ X : CochainComplex B ℤ,
      tdB.app (DerivedCategory.Q.obj X) ≫
        qB.mapDerivedCategory.map (Vn.mapDerivedCategoryFactors.hom.app X) ≫
        qB.mapDerivedCategoryFactors.hom.app ((Vn.mapHomologicalComplex (.up ℤ)).obj X) =
      Vm.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex tB (.up ℤ)).app X))
    (ht : ∀ X : A,
      tB.app (L.obj X) ≫ qB.map (cn.hom.app X) ≫ s.hom.app (Un.obj X) =
        cm.hom.app X ≫ Lm.map (tA.app X))
    (X : DerivedCategory A) :
    tdB.app (L.mapDerivedCategory.obj X) ≫
        qB.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso cn).hom.app X) ≫
        (Functor.mapDerivedCategorySquareIso s).hom.app (Un.mapDerivedCategory.obj X) =
      (Functor.mapDerivedCategorySquareIso cm).hom.app X ≫
        Lm.mapDerivedCategory.map (tdA.app X) := by
  have cnfac := Functor.exactSquare_fac cn
  have cmfac := Functor.exactSquare_fac cm
  have sfac := Functor.exactSquare_fac s
  generalize hcnD : Functor.mapDerivedCategorySquareIso cn = cnD at *
  generalize hcmD : Functor.mapDerivedCategorySquareIso cm = cmD at *
  generalize hsD : Functor.mapDerivedCategorySquareIso s = sD at *
  let left : L.mapDerivedCategory ⋙ Vm.mapDerivedCategory ⟶
      Un.mapDerivedCategory ⋙ qA.mapDerivedCategory ⋙ Lm.mapDerivedCategory :=
    Functor.whiskerLeft L.mapDerivedCategory tdB ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight cnD.hom qB.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Un.mapDerivedCategory sD.hom
  let right : L.mapDerivedCategory ⋙ Vm.mapDerivedCategory ⟶
      Un.mapDerivedCategory ⋙ qA.mapDerivedCategory ⋙ Lm.mapDerivedCategory :=
    cmD.hom ≫ Functor.whiskerRight tdA Lm.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom
  have eq : left = right := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro M
    let LM := (L.mapHomologicalComplex (.up ℤ)).obj M
    let UnM := (Un.mapHomologicalComplex (.up ℤ)).obj M
    dsimp only [left, right, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    change tdB.app (L.mapDerivedCategory.obj (DerivedCategory.Q.obj M)) ≫
        qB.mapDerivedCategory.map (cnD.hom.app (DerivedCategory.Q.obj M)) ≫
        sD.hom.app (Un.mapDerivedCategory.obj (DerivedCategory.Q.obj M)) =
      cmD.hom.app (DerivedCategory.Q.obj M) ≫
        Lm.mapDerivedCategory.map (tdA.app (DerivedCategory.Q.obj M))
    apply (cancel_mono
      (Lm.mapDerivedCategory.map
        (qA.mapDerivedCategory.map (Un.mapDerivedCategoryFactors.hom.app M)) ≫
        Lm.mapDerivedCategory.map (qA.mapDerivedCategoryFactors.hom.app UnM) ≫
        Lm.mapDerivedCategoryFactors.hom.app
          ((qA.mapHomologicalComplex (.up ℤ)).obj UnM))).1
    simp only [Category.assoc]
    have ns := sD.hom.naturality (Un.mapDerivedCategoryFactors.hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at ns
    rw [← reassoc_of% ns]
    erw [sfac UnM]
    repeat' erw [← qB.mapDerivedCategory.map_comp_assoc]
    repeat' erw [Category.assoc]
    erw [cnfac M]
    repeat' erw [qB.mapDerivedCategory.map_comp]
    repeat' erw [Category.assoc]
    have nq := qB.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex cn.hom (.up ℤ)).app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at nq
    erw [reassoc_of% nq]
    have nt := tdB.naturality (L.mapDerivedCategoryFactors.hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at nt
    erw [← reassoc_of% nt, reassoc_of% (htB LM)]
    repeat' erw [← Lm.mapDerivedCategory.map_comp_assoc]
    repeat' erw [Category.assoc]
    erw [htA]
    repeat' erw [Lm.mapDerivedCategory.map_comp]
    repeat' erw [Category.assoc]
    have nl := Lm.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex tA (.up ℤ)).app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at nl
    erw [nl]
    erw [reassoc_of% (cmfac M)]
    repeat' erw [Category.assoc]
    repeat' erw [← DerivedCategory.Q.map_comp]
    repeat' apply congrArg (fun t ↦ _ ≫ t)
    apply congrArg DerivedCategory.Q.map
    ext i
    exact ht (M.X i)
  simpa only [left, right, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using NatTrans.congr_app eq X


set_option maxHeartbeats 500000 in
-- This generic calculation localizes all six faces of an exact-functor cube.
private theorem normalized_derived_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [Abelian A'] [Abelian B'] [Abelian C'] [Abelian D']
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory A'] [HasDerivedCategory B']
    [HasDerivedCategory C'] [HasDerivedCategory D']
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions B'] [Abelian.HasKInjectiveResolutions D']
    (F : A ⥤ B) (R : B ⥤ A) (K : C ⥤ D) (S : D ⥤ C)
    (F' : A' ⥤ B') (R' : B' ⥤ A') (K' : C' ⥤ D') (S' : D' ⥤ C')
    (G : A ⥤ C) (H : B ⥤ D) (G' : A' ⥤ C') (H' : B' ⥤ D')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    [F.Additive] [K.Additive] [F'.Additive] [K'.Additive]
    [R.Additive] [S.Additive] [R'.Additive] [S'.Additive]
    [G.Additive] [H.Additive] [G'.Additive] [H'.Additive]
    [a.Additive] [b.Additive] [c.Additive] [d.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    [PreservesFiniteLimits a] [PreservesFiniteColimits a]
    [PreservesFiniteLimits b] [PreservesFiniteColimits b]
    [PreservesFiniteLimits c] [PreservesFiniteColimits c]
    [PreservesFiniteLimits d] [PreservesFiniteColimits d]
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : a ⋙ G' ≅ G ⋙ c)
    (pH : b ⋙ H' ≅ H ⋙ d) (pK : K ⋙ d ≅ c ⋙ K')
    (e : F ⋙ H ≅ G ⋙ K) (e' : F' ⋙ H' ≅ G' ⋙ K')
    (comm : ∀ X : A,
      H'.map (pF.hom.app X) ≫ e'.hom.app (a.obj X) ≫ K'.map (pG.hom.app X) =
        pH.hom.app (F.obj X) ≫ d.map (e.hom.app X) ≫ pK.hom.app (G.obj X))
    (Z : DerivedCategory B) :
    c.mapDerivedCategory.map ((SystemEvaluationNormalization.derivedMate adj adjK e).app Z) ≫
        (SystemEvaluationNormalization.derivedMate adjK adjK' pK).app
          (H.mapDerivedCategory.obj Z) =
      (Functor.mapDerivedCategorySquareIso pG).inv.app (R.rightDerivedFunctor.obj Z) ≫
        G'.mapDerivedCategory.map
          ((SystemEvaluationNormalization.derivedMate adj adj' pF).app Z) ≫
        (SystemEvaluationNormalization.derivedMate adj' adjK' e').app
          (b.mapDerivedCategory.obj Z) ≫
        S'.rightDerivedFunctor.map ((Functor.mapDerivedCategorySquareIso pH).hom.app Z) := by
  let sd := Functor.mapDerivedCategorySquareIso pF
  let ca := Functor.mapDerivedCategorySquareIso e'
  let cb := Functor.mapDerivedCategorySquareIso e
  let sy := Functor.mapDerivedCategorySquareIso pG
  let sx := Functor.mapDerivedCategorySquareIso pH
  let sl := Functor.mapDerivedCategorySquareIso pK
  have cube := Functor.mapDerivedCategory_exactCube
    F b H' a F' G' K' G c H d K pF e' pG pH e pK comm
  have hc (X : DerivedCategory A) :
      K'.mapDerivedCategory.map (sy.hom.app X) ≫
          sl.inv.app (G.mapDerivedCategory.obj X) ≫
          d.mapDerivedCategory.map (cb.inv.app X) =
        ca.inv.app (a.mapDerivedCategory.obj X) ≫
          H'.mapDerivedCategory.map (sd.inv.app X) ≫
          sx.hom.app (F.mapDerivedCategory.obj X) := by
    have cx := NatTrans.congr_app cube X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at cx
    change H'.mapDerivedCategory.map (sd.hom.app X) ≫
        ca.hom.app (a.mapDerivedCategory.obj X) ≫
        K'.mapDerivedCategory.map (sy.hom.app X) =
      sx.hom.app (F.mapDerivedCategory.obj X) ≫
        d.mapDerivedCategory.map (cb.hom.app X) ≫
        sl.hom.app (G.mapDerivedCategory.obj X) at cx
    apply (cancel_epi
      (H'.mapDerivedCategory.map (sd.hom.app X) ≫
        ca.hom.app (a.mapDerivedCategory.obj X))).1
    simp only [Category.assoc]
    rw [reassoc_of% cx]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [Functor.map_id, Category.comp_id, Functor.map_id, Category.id_comp]
  have h := exchangeMate_cube adj.mapDerivedCategoryRightDerivedAdjunction
    adjK.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction
    adjK'.mapDerivedCategoryRightDerivedAdjunction
    a.mapDerivedCategory b.mapDerivedCategory c.mapDerivedCategory d.mapDerivedCategory
    sd sy.symm sx.symm sl cb.inv ca.inv hc Z
  have hh := congrArg (fun t ↦ t ≫ S'.rightDerivedFunctor.map (sx.hom.app Z)) h
  simp only [Iso.symm_hom, Category.assoc] at hh
  erw [← S'.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app,
    S'.rightDerivedFunctor.map_id, Category.comp_id] at hh
  simpa only [SystemEvaluationNormalization.derivedMate, Functor.comp_obj,
    sd, ca, cb, sl, sx, sy] using hh


private theorem faithful_triangle
    {V W : Type*} [Category V] [Category W] (U : V ⥤ W) [U.Faithful]
    {X0 X1 X2 X3 X4 : V} {Y0 Y1 : W}
    (t : X0 ⟶ X1) (e : X1 ⟶ X2) (r : X2 ⟶ X3)
    (em : X0 ⟶ X4) (hm : X4 ⟶ X3)
    (un : U.obj X2 ≅ Y0) (um0 : U.obj X4 ≅ Y1) (um1 : U.obj X3 ≅ Y0)
    (ty : Y1 ⟶ Y0)
    (ht : U.map em ≫ um0.hom ≫ ty ≫ un.inv = U.map t ≫ U.map e)
    (hr : U.map r ≫ um1.hom = un.hom)
    (hn : U.map hm ≫ um1.hom = um0.hom ≫ ty) : t ≫ e ≫ r = em ≫ hm := by
  apply U.map_injective
  apply (cancel_mono um1.hom).1
  simp only [Functor.map_comp, Category.assoc]
  rw [hr, hn]
  rw [← Category.assoc (U.map t), ← ht]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (AY : Sheaf J CommRingCat.{w}) (AX : Sheaf K CommRingCat.{w})
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (aY : (Functor.const ℕᵒᵖ).obj AY ⟶ BY)
  (aX : (Functor.const ℕᵒᵖ).obj AX ⟶ BX)
  (uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (IA : AlgebraicInverseImage uTop.inverse AY AX)
  (IB : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n)))
  (FB : SystemGeometricInverseImageData BY BX uTop IB)
  (FA : SystemGeometricInverseImageData
    ((Functor.const ℕᵒᵖ).obj AY) ((Functor.const ℕᵒᵖ).obj AX) uTop (fun _ ↦ IA))


set_option maxHeartbeats 500000 in
-- Unfolding the underlying semilinear module functors exceeds the default allowance.
private theorem ordinary_transition
    (d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA)
    {n m : ℕ} (h : n ≤ m) (M : StrictRingSystem BY) :
    (strictSystemTransition BX h).app (FB.functor.obj M) ≫
        (systemRestriction BX h).map ((FB.evaluation n).hom.app M) ≫
        (d.restriction h).hom.app ((systemEvaluation BY n).obj M) =
      (FB.evaluation m).hom.app M ≫
        (FB.levelFunctor m).map ((strictSystemTransition BY h).app M) := by
  exact CategoryTheory.faithful_triangle (systemGeometricUnderlying BX m)
    ((strictSystemTransition BX h).app (FB.functor.obj M))
    ((systemRestriction BX h).map ((FB.evaluation n).hom.app M))
    ((d.restriction h).hom.app ((systemEvaluation BY n).obj M))
    ((FB.evaluation m).hom.app M)
    ((FB.levelFunctor m).map ((strictSystemTransition BY h).app M))
    ((IB n).moduleUnderlying.app (M.level n))
    ((IB m).moduleUnderlying.app (M.level m))
    ((IB m).moduleUnderlying.app ((systemRestriction BY h).obj (M.level n)))
    (uTop.inverse.map ((systemGeometricUnderlying BY m).map (M.transition h)))
    (FB.transition M h) (d.restrictionUnderlying h (M.level n))
    ((IB m).moduleUnderlying.hom.naturality (M.transition h))


private theorem localized_transition
    (d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA)
    {n m : ℕ} (h : n ≤ m) (M : DerivedCategory (StrictRingSystem BY)) :
    (systemDerivedTransition BX h).app (FB.functor.mapDerivedCategory.obj M) ≫
        (systemRestriction BX h).mapDerivedCategory.map
          ((FB.derivedEvaluation n).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso (d.restriction h)).hom.app
          ((derivedSystemEvaluation BY n).obj M) =
      (FB.derivedEvaluation m).hom.app M ≫
        (FB.levelFunctor m).mapDerivedCategory.map ((systemDerivedTransition BY h).app M) := by
  exact CategoryTheory.localized_transition_square FB.functor
    (FB.levelFunctor n) (FB.levelFunctor m)
    (systemEvaluation BY n) (systemEvaluation BX n)
    (systemEvaluation BY m) (systemEvaluation BX m)
    (systemRestriction BY h) (systemRestriction BX h)
    (FB.evaluation n) (FB.evaluation m) (d.restriction h)
    (strictSystemTransition BY h) (strictSystemTransition BX h)
    (systemDerivedTransition BY h) (systemDerivedTransition BX h)
    (systemDerivedTransition_rep BY h) (systemDerivedTransition_rep BX h)
    (fun N ↦ ordinary_transition AY AX BY BX aY aX uTop IA IB FB FA d h N) M


variable (HB : StrictRingSystem BX ⥤ StrictRingSystem BY) [HB.Additive]
  (HA : StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX) ⥤
    StrictRingSystem ((Functor.const ℕᵒᵖ).obj AY)) [HA.Additive]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX))]
  (adjB : FB.functor ⊣ HB) (adjA : FA.functor ⊣ HA)
  (Hn : ∀ n : ℕ, systemLevel BX n ⥤ systemLevel BY n)
  [∀ n : ℕ, (Hn n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n)]
  (adjn : ∀ n : ℕ, FB.levelFunctor n ⊣ Hn n)
  (H0 : systemLevel ((Functor.const ℕᵒᵖ).obj AX) 0 ⥤
    systemLevel ((Functor.const ℕᵒᵖ).obj AY) 0) [H0.Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel ((Functor.const ℕᵒᵖ).obj AX) n)]
  (adj0 : FA.levelFunctor 0 ⊣ H0)

set_option maxHeartbeats 500000 in
-- The six faces contain nested system, evaluation, and derived-functor comparisons.
private theorem scalar_coherence
    (d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA)
    (n : ℕ) (Z : DerivedCategory (StrictRingSystem BX)) :
        (singletonLevelRestriction aY n).mapDerivedCategory.map
            ((SystemEvaluationNormalization.derivedMate adjB (adjn n) (FB.evaluation n)).app Z) ≫
          (SystemEvaluationNormalization.derivedMate (adjn n) adj0 (d.level n)).app
            ((derivedSystemEvaluation BX n).obj Z) =
        (systemNormalizationDerivedRestrictionEvaluation aY n).inv.app
            (HB.rightDerivedFunctor.obj Z) ≫
          (derivedSystemEvaluation ((Functor.const ℕᵒᵖ).obj AY) n).map
            ((SystemEvaluationNormalization.derivedMate adjB adjA d.scalar).app Z) ≫
          (CategoryTheory.SystemEvaluationNormalization.derivedMate adjA adj0 (FA.evaluation n)).app
              ((systemNormalizationRestriction aX).mapDerivedCategory.obj Z) ≫
          H0.rightDerivedFunctor.map
            ((systemNormalizationDerivedRestrictionEvaluation aX n).hom.app Z) := by
  simpa only [systemNormalizationDerivedRestrictionEvaluation, derivedSystemEvaluation] using
    CategoryTheory.normalized_derived_cube
      FB.functor HB (FB.levelFunctor n) (Hn n)
      FA.functor HA (FA.levelFunctor 0) H0
      (systemEvaluation BY n) (systemEvaluation BX n)
      (systemEvaluation ((Functor.const ℕᵒᵖ).obj AY) n)
      (systemEvaluation ((Functor.const ℕᵒᵖ).obj AX) n)
      (systemNormalizationRestriction aY) (systemNormalizationRestriction aX)
      (singletonLevelRestriction aY n) (singletonLevelRestriction aX n)
      adjB (adjn n) adjA adj0 d.scalar
      (systemNormalizationRestrictionEvaluation aY n)
      (systemNormalizationRestrictionEvaluation aX n)
      (d.level n) (FB.evaluation n) (FA.evaluation n)
      (fun M ↦ d.scalarEvaluation M n) Z

omit [Abelian.HasKInjectiveResolutions
    (StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX))]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions
    (systemLevel ((Functor.const ℕᵒᵖ).obj AX) n)] in
private theorem transition_coherence
    (d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA)
    {n m : ℕ} (h : n ≤ m) (Z : DerivedCategory (StrictRingSystem BX)) :
    (systemDerivedTransition BY h).app (HB.rightDerivedFunctor.obj Z) ≫
        (systemRestriction BY h).mapDerivedCategory.map
          ((SystemEvaluationNormalization.derivedMate adjB (adjn n)
            (FB.evaluation n)).app Z) ≫
        (SystemEvaluationNormalization.derivedMate (adjn n) (adjn m)
          (d.restriction h)).app ((derivedSystemEvaluation BX n).obj Z) =
      (SystemEvaluationNormalization.derivedMate adjB (adjn m) (FB.evaluation m)).app Z ≫
        (Hn m).rightDerivedFunctor.map ((systemDerivedTransition BX h).app Z) := by
  exact CategoryTheory.restriction_mate_transition
    adjB.mapDerivedCategoryRightDerivedAdjunction
    (adjn n).mapDerivedCategoryRightDerivedAdjunction
    (adjn m).mapDerivedCategoryRightDerivedAdjunction
    (FB.derivedEvaluation n)
    (FB.derivedEvaluation m)
    (Functor.mapDerivedCategorySquareIso (d.restriction h))
    (systemDerivedTransition BY h) (systemDerivedTransition BX h)
    (fun M ↦ localized_transition AY AX BY BX aY aX uTop IA IB FB FA d h M) Z

/-- Prove the evaluation and transition mate equations for a normalization datum.
Source: Stacks Project, Tags 03D2, 0D6E and 07A6.
(blueprint: lem-route-system-restriction-mate-coherence-equations).

Proof: Localize the scalar/evaluation cube and apply the mate-cube theorem, cancelling
the comparison isomorphisms. Prove the ordinary transition square by the faithful
underlying-sheaf functor and the prescribed underlying transition equations. Localize
it using the exact-square factorization maps and the derived-transition representative
equation. Transpose the proposed mate equation under the level adjunction: the
mate-counit equations and naturality reduce the two transposes to that localized
transition square. Injectivity of adjunction transposition concludes. -/
theorem SystemRestrictionMateCoherenceEquations
    :
    ∀ d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA,
      (∀ (n : ℕ) (Z : DerivedCategory (StrictRingSystem BX)),
        (singletonLevelRestriction aY n).mapDerivedCategory.map
            ((SystemEvaluationNormalization.derivedMate adjB (adjn n) (FB.evaluation n)).app Z) ≫
          (SystemEvaluationNormalization.derivedMate (adjn n) adj0 (d.level n)).app
            ((derivedSystemEvaluation BX n).obj Z) =
        (systemNormalizationDerivedRestrictionEvaluation aY n).inv.app
            (HB.rightDerivedFunctor.obj Z) ≫
          (derivedSystemEvaluation ((Functor.const ℕᵒᵖ).obj AY) n).map
            ((SystemEvaluationNormalization.derivedMate adjB adjA d.scalar).app Z) ≫
          (CategoryTheory.SystemEvaluationNormalization.derivedMate adjA adj0 (FA.evaluation n)).app
              ((systemNormalizationRestriction aX).mapDerivedCategory.obj Z) ≫
          H0.rightDerivedFunctor.map
            ((systemNormalizationDerivedRestrictionEvaluation aX n).hom.app Z)) ∧
      (∀ {n m : ℕ} (h : n ≤ m) (Z : DerivedCategory (StrictRingSystem BX)),
        (systemDerivedTransition BY h).app (HB.rightDerivedFunctor.obj Z) ≫
            (systemRestriction BY h).mapDerivedCategory.map
              ((SystemEvaluationNormalization.derivedMate adjB (adjn n)
                (FB.evaluation n)).app Z) ≫
            (SystemEvaluationNormalization.derivedMate (adjn n) (adjn m)
              (d.restriction h)).app
            ((derivedSystemEvaluation BX n).obj Z) =
          (SystemEvaluationNormalization.derivedMate adjB (adjn m) (FB.evaluation m)).app Z ≫
            (Hn m).rightDerivedFunctor.map ((systemDerivedTransition BX h).app Z)) := by
  intro d
  exact ⟨fun n Z ↦ scalar_coherence AY AX BY BX aY aX uTop IA IB FB FA
      HB HA adjB adjA Hn adjn H0 adj0 d n Z,
    fun h Z ↦ transition_coherence AY AX BY BX aY aX uTop IA IB FB FA HB adjB Hn adjn d h Z⟩

end SheafOfModules
