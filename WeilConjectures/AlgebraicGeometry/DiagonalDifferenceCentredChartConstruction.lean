/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalDifferenceFrameData
import all WeilConjectures.AlgebraicGeometry.SectionReesBaseChangeEtale
import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import all WeilConjectures.AlgebraicGeometry.ChartNormalDifferential
import all WeilConjectures.AlgebraicGeometry.ReesConeNormalizedExistence
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import all WeilConjectures.AlgebraicGeometry.DiagonalDifferenceFrameChange

/-! # Assembly of the centred normalized Rees chart

Source: orientation chart proof, Steps 1 and 3; Stacks 0634--0635 and 08S2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.DiagonalDifferenceReesFrame

attribute [local irreducible] SectionReesBaseChange.pairMap
  Scheme.Hom.deformationSpaceToAffineSpace

set_option backward.isDefEq.respectTransparency false in
private theorem difference_etale {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    (c : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale c]
    (hc : c ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    Etale (AffineSpace.homOfVector (pullback.fst h h)
      (fun i ↦ (pullback.snd h h).appTop (c.appTop (AffineSpace.coord V i)) -
        (pullback.fst h h).appTop (c.appTop (AffineSpace.coord V i)))) := by
  let I := ULift.{u} (Fin d)
  let x (i : I) := c.appTop (AffineSpace.coord V i)
  let z := AffineSpace.homOfVector (pullback.fst h h)
    (fun i ↦ (pullback.snd h h).appTop (x i))
  have hz : z ≫ (AffineSpace I U ↘ U) = pullback.fst h h :=
    AffineSpace.homOfVector_over _ _
  have hzmap : z ≫ AffineSpace.map I h = pullback.snd h h ≫ c := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, hz, Category.assoc, hc,
        pullback.condition]
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.map_appTop_coord]
      exact AffineSpace.homOfVector_appTop_coord _ _ _
  have houter : IsPullback (pullback.snd h h) (z ≫ (AffineSpace I U ↘ U))
      (c ≫ (AffineSpace I V ↘ V)) h := by
    rw [hz, hc]
    exact (IsPullback.of_hasPullback h h).flip
  have hzpb : IsPullback (pullback.snd h h) z c (AffineSpace.map I h) :=
    IsPullback.of_bot houter hzmap.symm (AffineSpace.isPullback_map h)
  have : Etale z := MorphismProperty.of_isPullback hzpb inferInstance
  have : IsIso (AffineSpace.translation (-x)) := by
    refine ⟨AffineSpace.translation x, ?_, ?_⟩
    · rw [← AffineSpace.translation_add, neg_add_cancel, AffineSpace.translation_zero]
    · rw [← AffineSpace.translation_add, add_neg_cancel, AffineSpace.translation_zero]
  have he : z ≫ AffineSpace.translation (-x) =
      AffineSpace.homOfVector (pullback.fst h h)
        (fun i ↦ (pullback.snd h h).appTop (x i) -
          (pullback.fst h h).appTop (x i)) := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc, AffineSpace.translation_over, hz,
        AffineSpace.homOfVector_over]
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.translation_appTop_coord, map_add,
        AffineSpace.homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord]
      have hzv : z.appTop ((AffineSpace I U ↘ U).appTop ((-x) i)) =
          (pullback.fst h h).appTop ((-x) i) := by
        exact congrArg (fun f ↦ f.appTop ((-x) i)) hz
      rw [hzv]
      simp only [Pi.neg_apply, map_neg, sub_eq_add_neg]
  rw [← he]
  infer_instance

private theorem map_diagonal {X U A V : Scheme.{u}} (p : A ⟶ V) (c : U ⟶ A)
    (a : X ⟶ pullback (c ≫ p) (c ≫ p)) (b : X ⟶ U)
    (h₁ : a ≫ pullback.fst (c ≫ p) (c ≫ p) = b)
    (h₂ : a ≫ pullback.snd (c ≫ p) (c ≫ p) ≫ c = b ≫ c) :
    a ≫ pullback.map (c ≫ p) (c ≫ p) p p c c (𝟙 V) (by simp) (by simp) =
      b ≫ c ≫ pullback.diagonal p := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    exact congrArg (· ≫ c) h₁
  · simpa only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
      Category.comp_id] using h₂

set_option backward.isDefEq.respectTransparency false in
private theorem centred_neighbourhood {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    [IsSeparated h] (c : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale c]
    (hc : c ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    ∃ (O : (pullback h h).Opens) (s : U ⟶ O.toScheme),
      s ≫ O.ι = pullback.diagonal h ∧
      Etale (O.ι ≫ AffineSpace.homOfVector (pullback.fst h h)
        (fun i ↦ (pullback.snd h h).appTop (c.appTop (AffineSpace.coord V i)) -
          (pullback.fst h h).appTop (c.appTop (AffineSpace.coord V i)))) ∧
      IsPullback s (𝟙 U) (O.ι ≫ AffineSpace.homOfVector (pullback.fst h h)
        (fun i ↦ (pullback.snd h h).appTop (c.appTop (AffineSpace.coord V i)) -
          (pullback.fst h h).appTop (c.appTop (AffineSpace.coord V i))))
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) U) := by
  subst h
  let I := ULift.{u} (Fin d)
  let p := AffineSpace I V ↘ V
  let h := c ≫ p
  let E := pullback.map h h p p c c (𝟙 V) (by simp only [Category.comp_id]; rfl)
    (by simp only [Category.comp_id]; rfl)
  let D := AffineSpace.homOfVector (pullback.fst h h)
    (fun i ↦ (pullback.snd h h).appTop (c.appTop (AffineSpace.coord V i)) -
      (pullback.fst h h).appTop (c.appTop (AffineSpace.coord V i)))
  obtain ⟨O, s, _, hs, H, _, _⟩ := ChartNormalDifferential.chartGeometry p c
  have : Etale D := difference_etale d h c rfl
  have hsp : s ≫ O.ι ≫ pullback.fst h h = 𝟙 U := by
    change (s ≫ O.ι) ≫ pullback.fst h h = 𝟙 U
    rw [hs, pullback.diagonal_fst]
  have hD : D ≫ (AffineSpace I U ↘ U) = pullback.fst h h :=
    AffineSpace.homOfVector_over _ _
  have hzero : s ≫ (O.ι ≫ D) = (𝟙 U) ≫ AffineSpace.zeroSection I U := by
    apply AffineSpace.hom_ext
    · change s ≫ O.ι ≫ D ≫ (AffineSpace I U ↘ U) =
        (𝟙 U) ≫ AffineSpace.zeroSection I U ≫ (AffineSpace I U ↘ U)
      rw [hD, AffineSpace.zeroSection_over, Category.comp_id, hsp]
    · intro i
      change (s ≫ O.ι ≫ AffineSpace.homOfVector (pullback.fst h h) _).appTop
        (AffineSpace.coord U i) = ((𝟙 U) ≫ AffineSpace.zeroSection I U).appTop
          (AffineSpace.coord U i)
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.homOfVector_appTop_coord, AffineSpace.zeroSection_appTop_coord,
        map_sub, Scheme.Hom.id_appTop, id_apply]
      have hf := congrArg (fun f ↦ f.appTop (c.appTop (AffineSpace.coord V i)))
        (show s ≫ O.ι ≫ pullback.fst h h = 𝟙 U from hsp)
      have hsnd : s ≫ O.ι ≫ pullback.snd h h = 𝟙 U := by
        rw [← Category.assoc, hs, pullback.diagonal_snd]
      have hg := congrArg (fun f ↦ f.appTop (c.appTop (AffineSpace.coord V i))) hsnd
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Scheme.Hom.id_appTop, id_apply] using sub_eq_zero.mpr (hg.trans hf.symm)
  refine ⟨O, s, hs, inferInstance, ⟨⟨hzero⟩, ⟨?_⟩⟩⟩
  refine PullbackCone.IsLimit.mk _ (fun t ↦ t.snd) (fun t ↦ ?_)
    (fun t ↦ by simp) (fun t l hl₁ hl₂ ↦ by simpa using hl₂)
  have htbase : t.fst ≫ O.ι ≫ pullback.fst h h = t.snd := by
    have ht := congrArg (· ≫ (AffineSpace I U ↘ U)) t.condition
    change (t.fst ≫ O.ι ≫ D) ≫ (AffineSpace I U ↘ U) =
      (t.snd ≫ AffineSpace.zeroSection I U) ≫ (AffineSpace I U ↘ U) at ht
    simpa only [Category.assoc, hD, AffineSpace.zeroSection_over, Category.comp_id] using ht
  have htcoord (i : I) : (t.fst ≫ O.ι ≫ pullback.snd h h ≫ c).appTop
      (AffineSpace.coord V i) = (t.snd ≫ c).appTop (AffineSpace.coord V i) := by
    have ht := congrArg (fun f ↦ f.appTop (AffineSpace.coord U i)) t.condition
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.homOfVector_appTop_coord, AffineSpace.zeroSection_appTop_coord,
      map_sub, map_zero] at ht
    have htbase' := congrArg (fun f ↦ f.appTop (c.appTop (AffineSpace.coord V i))) htbase
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at htbase' ⊢
    exact (sub_eq_zero.mp ht).trans htbase'
  have htc : t.fst ≫ O.ι ≫ pullback.snd h h ≫ c = t.snd ≫ c := by
    apply AffineSpace.hom_ext
    · change (t.fst ≫ O.ι ≫ pullback.snd h h) ≫ h = t.snd ≫ h
      calc
        (t.fst ≫ O.ι ≫ pullback.snd h h) ≫ h =
            (t.fst ≫ O.ι) ≫ (pullback.snd h h ≫ h) := Category.assoc _ _ _
        _ = (t.fst ≫ O.ι) ≫ (pullback.fst h h ≫ h) :=
          congrArg ((t.fst ≫ O.ι) ≫ ·) (pullback.condition (f := h) (g := h)).symm
        _ = t.snd ≫ h := by rw [← Category.assoc, Category.assoc t.fst O.ι _, htbase]
    · exact htcoord
  have hte : t.fst ≫ (O.ι ≫ E) = (t.snd ≫ c) ≫ pullback.diagonal p := by
    simpa only [Category.assoc] using map_diagonal p c (t.fst ≫ O.ι) t.snd htbase htc
  let l := H.lift t.fst (t.snd ≫ c) hte
  have hls : l ≫ s = t.fst := H.lift_fst _ _ _
  have hl : l = t.snd := by
    rw [← htbase, ← hls]
    simp only [Category.assoc, hsp, Category.comp_id]
  exact hl ▸ hls

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pair_coordinate {S X : Scheme.{u}} [IsAffine S] (I : Type u)
    (s : S ⟶ X) [IsClosedImmersion s] (e : X ⟶ AffineSpace I S)
    (w : s ≫ e = (𝟙 S) ≫ AffineSpace.zeroSection I S)
    (A : X.AffineZariskiSite) (i : I) :
    ∃ hi : e.appLE ⊤ A.1 (by simp) (AffineSpace.coord S i) ∈ s.ker.siteIdeal A,
      (colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
        s.ker.coequifibered_toReesPresheaf).functor A ≫
          SectionReesBaseChange.pairMap (AffineSpace.zeroSection I S) s e (𝟙 S) w ≫
            Scheme.Hom.deformationSpaceToAffineSpace I S).appTop
              (AffineSpace.coord (AffineSpace (ULift.{u} (Fin 1)) S) i) =
        (Scheme.ΓSpecIso (s.ker.reesPresheaf.obj (op A))).inv
          ⟨LaurentPolynomial.C (e.appLE ⊤ A.1 (by simp) (AffineSpace.coord S i)) *
            LaurentPolynomial.T (-1), Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra hi⟩ := by
  let B : (AffineSpace I S).AffineZariskiSite := ⟨⊤, isAffineOpen_top _⟩
  have hc := SectionReesBaseChange.pairMap_compatible
    (AffineSpace I S ↘ S) (e ≫ (AffineSpace I S ↘ S))
    (AffineSpace.zeroSection I S) s e (𝟙 S) w (by simp)
  obtain ⟨ν, l, hc, _⟩ := hc.2.2.2
  obtain ⟨ha, hchart⟩ := hc A B (by change A.1 ≤ e ⁻¹ᵁ ⊤; simp)
  have hi : e.appLE ⊤ A.1 (by simp) (AffineSpace.coord S i) ∈ s.ker.siteIdeal A := by
    apply ha
    have hm : AffineSpace.coord S i ∈ (AffineSpace.zeroSection I S).ker.siteIdeal B := by
      simp [B]
    exact Ideal.mem_map_of_mem _ hm
  refine ⟨hi, ?_⟩
  rw [← Category.assoc, hchart, Category.assoc,
    Scheme.Hom.ι_deformationSpaceToAffineSpace]
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Scheme.Hom.deformationSpaceToAffineSpaceChart, AffineSpace.homOfVector_appTop_coord]
  change ((Spec.map (CommRingCat.ofHom
    (((AffineSpace.zeroSection I S).ker.siteIdeal B).extendedReesAlgebraMap
      (e.appLE B.1 A.1 (by change A.1 ≤ e ⁻¹ᵁ ⊤; simp)).hom
      (s.ker.siteIdeal A) ha))).appTop)
      ((Scheme.ΓSpecIso _).inv (Scheme.Hom.uCoord I S B i)) = _
  erw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  congr 1
  apply Subtype.ext
  change LaurentPolynomial.mapRingHom _
      (LaurentPolynomial.C (Scheme.Hom.coordRes I S B i) * LaurentPolynomial.T (-1)) = _
  rw [map_mul, LaurentPolynomial.mapRingHom_C, LaurentPolynomial.mapRingHom_T]
  congr 2
  simp [Scheme.Hom.coordRes, B]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem parameter_coordinate {S X : Scheme.{u}} (g : X ⟶ S) (s : S ⟶ X)
    (A : X.AffineZariskiSite) :
    (colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
      s.ker.coequifibered_toReesPresheaf).functor A ≫
        Scheme.Hom.deformationSpaceProj g s).appTop
          (AffineSpace.coord S (ULift.up (0 : Fin 1))) =
      (Scheme.ΓSpecIso (s.ker.reesPresheaf.obj (op A))).inv
        (Ideal.extendedReesAlgebraT _) := by
  rw [Scheme.Hom.deformationSpaceProj, Scheme.IdealSheafData.deformationSpaceToPolynomialSpec,
    Scheme.AffineZariskiSite.ι_relativeGluingMap_assoc,
    Scheme.ι_polynomialSpecToAffineSpace_assoc,
    Scheme.polynomialSpecChart, AffineSpace.homOfVector_map,
    AffineSpace.comp_homOfVector, AffineSpace.homOfVector_appTop_coord,
    Function.comp_apply, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  congr 1
  exact Ideal.toExtendedReesAlgebra_X

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pair_comp {S X X' Y : Scheme.{u}} [IsAffine Y]
    (s : S ⟶ X) (s' : S ⟶ X') (z : S ⟶ Y)
    [IsClosedImmersion s] [IsClosedImmersion s'] [IsClosedImmersion z]
    (h : X' ⟶ X) (e : X ⟶ Y) (g : Y ⟶ S)
    (w : s' ≫ h = (𝟙 S) ≫ s) (v : s ≫ e = (𝟙 S) ≫ z)
    (wv : s' ≫ (h ≫ e) = (𝟙 S) ≫ z) :
    SectionReesBaseChange.pairMap s s' h (𝟙 S) w ≫
        SectionReesBaseChange.pairMap z s e (𝟙 S) v =
      SectionReesBaseChange.pairMap z s' (h ≫ e) (𝟙 S) wv := by
  let B : Y.AffineZariskiSite := ⟨⊤, isAffineOpen_top Y⟩
  have c₁ := SectionReesBaseChange.pairMap_compatible
    (e ≫ g) (h ≫ e ≫ g) s s' h (𝟙 S) w (by simp)
  have c₂ := SectionReesBaseChange.pairMap_compatible
    g (e ≫ g) z s e (𝟙 S) v (by simp)
  have c₃ := SectionReesBaseChange.pairMap_compatible
    g (h ≫ e ≫ g) z s' (h ≫ e) (𝟙 S) wv (by simp)
  obtain ⟨_, _, c₁, _⟩ := c₁.2.2.2
  obtain ⟨_, _, c₂, _⟩ := c₂.2.2.2
  obtain ⟨_, _, c₃, _⟩ := c₃.2.2.2
  apply Scheme.AffineZariskiSite.hom_ext_of_le_preimage h
    s'.ker.coequifibered_toReesPresheaf
  intro A' A hA
  obtain ⟨ha, h₁⟩ := c₁ A' A hA
  obtain ⟨hb, h₂⟩ := c₂ A B (by change A.1 ≤ e ⁻¹ᵁ ⊤; simp)
  obtain ⟨hc, h₃⟩ := c₃ A' B (by change A'.1 ≤ (h ≫ e) ⁻¹ᵁ ⊤; simp)
  rw [← Category.assoc, h₁, Category.assoc, h₂, h₃, ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro t
  apply Subtype.ext
  change LaurentPolynomial.mapRingHom _ (LaurentPolynomial.mapRingHom _ t.val) =
    LaurentPolynomial.mapRingHom _ t.val
  rw [LaurentPolynomial.mapRingHom_mapRingHom]
  congr 2
  change (e.appLE ⊤ A.1 (by simp) ≫ h.appLE A.1 A'.1 hA).hom = _
  rw [Scheme.Hom.appLE_comp_appLE]

set_option backward.isDefEq.respectTransparency false in
private theorem top_chart_iso {X : Scheme.{u}} [IsAffine X]
    (J : X.IdealSheafData) :
    IsIso (colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
      J.coequifibered_toReesPresheaf).functor ⟨⊤, isAffineOpen_top X⟩) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [← Scheme.AffineZariskiSite.toBase_preimage]
  exact Scheme.Hom.preimage_top _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem divided_coordinate_relation {S X : Scheme.{u}} [IsAffine S] [IsAffine X]
    (I : Type u) (g : X ⟶ S) (s : S ⟶ X) [IsClosedImmersion s]
    (e : X ⟶ AffineSpace I S)
    (w : s ≫ e = (𝟙 S) ≫ AffineSpace.zeroSection I S) (i : I) :
    (Scheme.Hom.deformationSpaceProj g s).appTop
        (AffineSpace.coord S (ULift.up (0 : Fin 1))) *
      (SectionReesBaseChange.pairMap (AffineSpace.zeroSection I S) s e (𝟙 S) w ≫
        Scheme.Hom.deformationSpaceToAffineSpace I S).appTop
          (AffineSpace.coord (AffineSpace (ULift.{u} (Fin 1)) S) i) =
      s.ker.deformationSpaceProj.appTop (e.appTop (AffineSpace.coord S i)) := by
  let A : X.AffineZariskiSite := ⟨⊤, isAffineOpen_top X⟩
  let j := colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
    s.ker.coequifibered_toReesPresheaf).functor A
  have : IsIso j := top_chart_iso s.ker
  apply (ConcreteCategory.bijective_of_isIso j.appTop).1
  rw [map_mul]
  change (j ≫ Scheme.Hom.deformationSpaceProj g s).appTop _ *
      (j ≫ SectionReesBaseChange.pairMap (AffineSpace.zeroSection I S) s e (𝟙 S) w ≫
        Scheme.Hom.deformationSpaceToAffineSpace I S).appTop _ =
      (j ≫ s.ker.deformationSpaceProj).appTop _
  obtain ⟨hi, hv⟩ := pair_coordinate I s e w A i
  rw [parameter_coordinate g s A, hv]
  rw [show j ≫ s.ker.deformationSpaceProj = Spec.map (s.ker.toReesPresheaf.app (op A)) ≫
      (isAffineOpen_top X).fromSpec from Scheme.AffineZariskiSite.ι_toBase _ A]
  have hfs : (isAffineOpen_top X).fromSpec.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
    change (isAffineOpen_top X).fromSpec.app ⊤ = _
    simp [IsAffineOpen.fromSpec_app_of_le]
  rw [Scheme.Hom.comp_appTop, hfs, CommRingCat.comp_apply]
  erw [Scheme.specMap_appTop_ΓSpecIso_inv]
  change (Scheme.ΓSpecIso (.of ((s.ker.siteIdeal A).extendedReesAlgebra))).inv _ *
    (Scheme.ΓSpecIso (.of ((s.ker.siteIdeal A).extendedReesAlgebra))).inv _ =
      (Scheme.ΓSpecIso (.of ((s.ker.siteIdeal A).extendedReesAlgebra))).inv _
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  change LaurentPolynomial.T 1 * (LaurentPolynomial.C
      (e.appLE ⊤ ⊤ (by simp) (AffineSpace.coord S i)) * LaurentPolynomial.T (-1)) = _
  rw [Scheme.Hom.appLE_top_top]
  change LaurentPolynomial.T 1 *
    (LaurentPolynomial.C (e.appTop (AffineSpace.coord S i)) * LaurentPolynomial.T (-1)) =
      LaurentPolynomial.C (e.appTop (AffineSpace.coord S i))
  rw [LaurentPolynomial.T_mul 1, LaurentPolynomial.mul_T_assoc]
  simp only [neg_add_cancel, LaurentPolynomial.T_zero, mul_one]

set_option backward.isDefEq.respectTransparency false in
private theorem open_centre_square {S W : Scheme.{u}} (a : S ⟶ W)
    (O : W.Opens) (s : S ⟶ O.toScheme) (hs : s ≫ O.ι = a) :
    IsPullback s (𝟙 S) O.ι a := by
  have hr : Set.range a ⊆ Set.range O.ι := by
    rw [← hs]
    rintro _ ⟨z, rfl⟩
    exact ⟨s z, rfl⟩
  have he : IsOpenImmersion.lift O.ι a hr = s := by
    apply (cancel_mono O.ι).mp
    exact (IsOpenImmersion.lift_fac _ _ _).trans hs.symm
  simpa only [he] using IsOpenImmersion.isPullback_lift_id a O.ι hr

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_model {S W : Scheme.{u}} (g : W ⟶ S) (a : S ⟶ W)
    [IsClosedImmersion a] (O : W.Opens) (s : S ⟶ O.toScheme)
    [IsClosedImmersion s] (hs : s ≫ O.ι = a) :
    ∃ m : s.ker.deformationSpace ≅ (a.ker.deformationSpaceProj ⁻¹ᵁ O).toScheme,
      m.hom ≫ (a.ker.deformationSpaceProj ⁻¹ᵁ O).ι =
        SectionReesBaseChange.pairMap a s O.ι (𝟙 S) (by simpa using hs) ∧
      m.hom ≫ (a.ker.deformationSpaceProj ⁻¹ᵁ O).ι ≫ a.ker.deformationSpaceProj =
        s.ker.deformationSpaceProj ≫ O.ι ∧
      m.hom ≫ (a.ker.deformationSpaceProj ⁻¹ᵁ O).ι ≫
        Scheme.Hom.deformationSpaceProj g a =
          Scheme.Hom.deformationSpaceProj (O.ι ≫ g) s := by
  let w : s ≫ O.ι = (𝟙 S) ≫ a := by simpa using hs
  let hJ : ∀ ⦃A' : O.toScheme.AffineZariskiSite⦄ ⦃A : W.AffineZariskiSite⦄
      (hA : A'.1 ≤ O.ι ⁻¹ᵁ A.1),
      (a.ker.siteIdeal A).map (O.ι.appLE A.1 A'.1 hA).hom ≤ s.ker.siteIdeal A' :=
    fun {A' A} hA ↦
      (a.ker.ideal_map_appLE_le_ideal_comap O.ι ⟨A.1, A.2⟩ ⟨A'.1, A'.2⟩ hA).trans
        (Scheme.IdealSheafData.le_def.mp
          (Scheme.Modules.closedImmersion_conormal_functorial s a O.ι (𝟙 S) w).1
            ⟨A'.1, A'.2⟩)
  let D := Scheme.IdealSheafData.extendedReesPullbackData O.ι a.ker s.ker hJ
  have hid : s.ker = a.ker.comap O.ι := by
    rw [← (open_centre_square a O s hs).isoPullback_hom_fst,
      Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hcov : ∀ x : O.toScheme, ∃ (A' : O.toScheme.AffineZariskiSite)
      (A : W.AffineZariskiSite) (hA : A'.1 ≤ O.ι ⁻¹ᵁ A.1), x ∈ A'.1 ∧
      IsPushout (O.ι.appLE A.1 A'.1 hA) (a.ker.toReesPresheaf.app (op A))
        (s.ker.toReesPresheaf.app (op A')) (D.map hA) := by
    intro x
    obtain ⟨A', hA', hx, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : O.toScheme.Opens) from trivial)
    let A : O.toScheme.AffineZariskiSite := ⟨A', hA'⟩
    exact ⟨A, Scheme.IdealSheafData.imageSite O.ι A,
      (O.ι.preimage_image_eq A.1).ge, hx,
      Scheme.IdealSheafData.isPushout_extendedReesPullbackData_imageSite
        O.ι a.ker s.ker hJ hid A⟩
  have H := D.isPullback_comparison a.ker.coequifibered_toReesPresheaf
    s.ker.coequifibered_toReesPresheaf hcov
  let m := H.isoIsPullback _ _ (isPullback_morphismRestrict a.ker.deformationSpaceProj O).flip
  have hm : m.hom ≫ (a.ker.deformationSpaceProj ⁻¹ᵁ O).ι =
      SectionReesBaseChange.pairMap a s O.ι (𝟙 S) w := by
    unfold SectionReesBaseChange.pairMap
    exact H.isoIsPullback_hom_fst _ _ _
  refine ⟨m, hm, ?_, ?_⟩
  · rw [← Category.assoc, hm]
    simpa only [SectionReesBaseChange.pairMap] using
      Scheme.IdealSheafData.deformationSpaceMap_toBase O.ι a.ker s.ker hJ
  · rw [← Category.assoc, hm]
    have hc := (SectionReesBaseChange.pairMap_compatible g (O.ι ≫ g) a s
      O.ι (𝟙 S) w (by simp)).1
    simpa using hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Given the canonical normal frame, the coordinate-difference neighbourhood and the
published normalized extended-Rees comparison assemble a `CentredChart`. Its fields are
fixed by the Cartesian zero square, the two fibre endpoints, and the Laurent formulas on
all affine Rees charts. Source: orientation chart proof, Steps 1 and 3
(blueprint: lem-pur-diagonal-difference-centred-chart). -/
theorem centred_chart_exists (k : Type u) [Field k]
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (aU : U ⟶ Spec (.of k)) (aV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType aU] [LocallyOfFiniteType aV]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [SmoothOfRelativeDimension d h]
    (hk : h ≫ aV = aU)
    (c : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale c]
    (hc : c ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h)
    (N : NormalFrame d h (fun i ↦ c.appTop (AffineSpace.coord V i))) :
    Nonempty (CentredChart d h (fun i ↦ c.appTop (AffineSpace.coord V i)) N) := by
  have := LocallyOfFiniteType.isLocallyNoetherian aU
  have : IsNoetherian U := {}
  have : LocallyOfFiniteType (h ≫ aV) := hk.symm ▸ inferInstance
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h aV
  let I := ULift.{u} (Fin d)
  let p := pullback.fst h h
  let a := pullback.diagonal h
  let D := AffineSpace.homOfVector p
    (fun i ↦ (pullback.snd h h).appTop (c.appTop (AffineSpace.coord V i)) -
      p.appTop (c.appTop (AffineSpace.coord V i)))
  obtain ⟨O, s, hs, he, H⟩ := centred_neighbourhood d h c hc
  have : IsClosedImmersion (s ≫ O.ι) := hs.symm ▸ inferInstance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s O.ι
  have hs₀ : s ≫ (O.ι ≫ p) = 𝟙 U := by
    rw [← Category.assoc, hs, pullback.diagonal_fst]
  have : Etale (O.ι ≫ D) := he
  have : O.toScheme.IsSeparated := ⟨by
    rw [← terminal.comp_from O.ι]
    infer_instance⟩
  have := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst h h)
  have : IsNoetherian (pullback h h) := {}
  have : NoetherianSpace O.toScheme := by
    change NoetherianSpace (O : Set ↥(pullback h h : Scheme.{u}))
    infer_instance
  have ha : a ≫ p = 𝟙 U := pullback.diagonal_fst h
  obtain ⟨m, hm, hma, hmp⟩ := restriction_model p a O s hs
  let z := AffineSpace.zeroSection I U
  let g := AffineSpace I U ↘ U
  have : SmoothOfRelativeDimension d g := by
    simpa [g, I, Nat.card_eq_fintype_card] using
      AffineSpace.smoothOfRelativeDimension_over I U
  have hz : z ≫ g = 𝟙 U := AffineSpace.zeroSection_over I U
  have hs₁ : s ≫ ((O.ι ≫ D) ≫ g) = 𝟙 U := by
    rw [Category.assoc, AffineSpace.homOfVector_over]
    exact hs₀
  let w : s ≫ (O.ι ≫ D) = (𝟙 U) ≫ z := H.w
  obtain ⟨hφpb, hφ, hφc, _, _⟩ := SectionReesBaseChange.etale d g z hz
    (O.ι ≫ D) s hs₁ w H
  let φ := SectionReesBaseChange.pairMap z s (O.ι ≫ D) (𝟙 U) w
  let F := φ ≫ Scheme.Hom.deformationSpaceToAffineSpace I U
  have hF : Etale F := inferInstance
  let wg : a ≫ D = (𝟙 U) ≫ z := by
    apply AffineSpace.hom_ext
    · change a ≫ D ≫ (AffineSpace I U ↘ U) =
        (𝟙 U) ≫ AffineSpace.zeroSection I U ≫ (AffineSpace I U ↘ U)
      rw [AffineSpace.homOfVector_over, AffineSpace.zeroSection_over, ha,
        Category.id_comp]
    · intro i
      change a.appTop ((AffineSpace.homOfVector p _).appTop (AffineSpace.coord U i)) =
        (AffineSpace.zeroSection I U).appTop (AffineSpace.coord U i)
      rw [AffineSpace.homOfVector_appTop_coord, AffineSpace.zeroSection_appTop_coord,
        map_sub]
      have h₁ := congrArg (fun t ↦ t.appTop (c.appTop (AffineSpace.coord V i))) ha
      have h₂ := congrArg (fun t ↦ t.appTop (c.appTop (AffineSpace.coord V i)))
        (pullback.diagonal_snd h)
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Scheme.Hom.id_appTop, id_apply] using sub_eq_zero.mpr (h₂.trans h₁.symm)
  let G := SectionReesBaseChange.pairMap z a D (𝟙 U) wg ≫
    Scheme.Hom.deformationSpaceToAffineSpace I U
  let R := a.ker.deformationSpaceProj ⁻¹ᵁ O
  let f := R.ι ≫ G
  have hmf : m.hom ≫ f = F := by
    dsimp only [f, G, F]
    rw [← Category.assoc, hm, ← Category.assoc]
    rw [pair_comp a s z O.ι D g (by simpa using hs) wg w]
  have hf : Etale f := by
    have : Etale (m.hom ≫ f) := hmf.symm ▸ hF
    have hfm : f = m.inv ≫ F := by rw [← hmf]; simp
    rw [hfm]
    infer_instance
  have hGo : G ≫ (AffineSpace I (AffineSpace (ULift.{u} (Fin 1)) U) ↘ _) =
      Scheme.Hom.deformationSpaceProj p a := by
    dsimp only [G]
    rw [Category.assoc, Scheme.Hom.deformationSpaceToAffineSpace_over]
    have hx := (SectionReesBaseChange.pairMap_compatible g p z a D (𝟙 U) wg
      (AffineSpace.homOfVector_over _ _)).1
    simpa only [AffineSpace.map_id, Category.comp_id] using hx
  have hfo : f ≫ (AffineSpace I (AffineSpace (ULift.{u} (Fin 1)) U) ↘ _) =
      R.ι ≫ Scheme.Hom.deformationSpaceProj p a := by
    dsimp only [f]
    rw [Category.assoc, hGo]
  let one₀ := O.ι ≫ Scheme.Hom.deformationSpaceOneFibre p a
  have hone : one₀ ≫ a.ker.deformationSpaceProj = O.ι := by
    dsimp only [one₀, Scheme.Hom.deformationSpaceOneFibre]
    rw [Category.assoc, Category.assoc, Scheme.Hom.deformationSpaceGeneric_toBase,
      pullback.lift_fst, Category.comp_id]
  have honeR : Set.range one₀ ⊆ Set.range R.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    change (one₀ ≫ a.ker.deformationSpaceProj) t ∈ O
    rw [hone]
    exact t.property
  let one := IsOpenImmersion.lift R.ι one₀ honeR
  have honeι : one ≫ R.ι = one₀ := IsOpenImmersion.lift_fac ..
  have hnbase : a.ker.normalConeToDeformationSpace ≫ a.ker.deformationSpaceProj =
      Scheme.Hom.purityNormalProjection a ≫ a := by
    rw [Scheme.IdealSheafData.normalConeToDeformationSpace,
      Scheme.AffineZariskiSite.relativeGluingMap_toBase _ _ _ rfl]
    exact (reesProjection_fac a).symm
  have hzeroR : Set.range a.ker.normalConeToDeformationSpace ⊆ Set.range R.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    change (a.ker.normalConeToDeformationSpace ≫ a.ker.deformationSpaceProj) t ∈ O
    rw [hnbase]
    change (Scheme.Hom.purityNormalProjection a ≫ pullback.diagonal h) t ∈ O
    rw [← hs]
    exact (s (Scheme.Hom.purityNormalProjection a t)).property
  let zero := IsOpenImmersion.lift R.ι a.ker.normalConeToDeformationSpace hzeroR
  have hzeroι : zero ≫ R.ι = a.ker.normalConeToDeformationSpace :=
    IsOpenImmersion.lift_fac ..
  refine ⟨{
    O := O
    s := s
    section_diagonal := hs
    etale := he
    zero_square := H
    deformation := f
    deformation_model := m
    model_ambient := hma
    model_parameter := hmp
    deformation_etale := hf
    deformation_over := hfo
    one := one
    one_inclusion := honeι
    one_endpoint := ?_
    zero := zero
    zero_inclusion := hzeroι
    zero_endpoint := ?_
    charts := ?_
    rank_zero := ?_
    rank_zero_deformation := ?_ }⟩
  · change one ≫ R.ι ≫ G = O.ι ≫ D ≫ AffineSpace.map I
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) U)
    rw [← Category.assoc, honeι]
    apply AffineSpace.hom_ext
    · rw [Category.assoc, hGo, Category.assoc,
        (Scheme.Hom.isPullback_deformationSpaceOneFibre p a).w,
        Category.assoc, Category.assoc, AffineSpace.map_over,
        ← Category.assoc D, AffineSpace.homOfVector_over]
    · intro i
      have hr := congrArg (fun x ↦ one₀.appTop x)
        (divided_coordinate_relation I p a D wg i)
      rw [map_mul] at hr
      have ht : one₀.appTop ((Scheme.Hom.deformationSpaceProj p a).appTop
          (AffineSpace.coord U (ULift.up (0 : Fin 1)))) = 1 := by
        change (one₀ ≫ Scheme.Hom.deformationSpaceProj p a).appTop _ = 1
        rw [Category.assoc, (Scheme.Hom.isPullback_deformationSpaceOneFibre p a).w]
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.oneSection, AffineSpace.homOfVector_appTop_coord,
          Pi.one_apply, map_one]
      rw [ht, one_mul] at hr
      change one₀.appTop (G.appTop _) = _ at hr ⊢
      rw [hr]
      change (one₀ ≫ a.ker.deformationSpaceProj ≫ D).appTop _ = _
      rw [← Category.assoc, hone]
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rw [AffineSpace.map_appTop_coord (AffineSpace.oneSection (ULift.{u} (Fin 1)) U) i]
  · intro q hq
    change zero ≫ R.ι ≫ G = q.hom ≫ N.normal.hom ≫
      AffineSpace.map I (AffineSpace.zeroSection (ULift.{u} (Fin 1)) U)
    rw [← Category.assoc, hzeroι]
    apply AffineSpace.hom_ext
    · rw [Category.assoc, hGo,
        (Scheme.Hom.isPullback_normalConeToDeformationSpace p a).w,
        Category.assoc, Category.assoc, AffineSpace.map_over]
      have hb : q.hom ≫ N.normal.hom ≫ (AffineSpace I U ↘ U) =
          Scheme.Hom.normalConeProj p a := by
        rw [N.normal_over]
        exact hq.1.trans (Scheme.Hom.purityNormalProjection_eq a p ha)
      simpa only [Category.assoc] using
        (congrArg (· ≫ AffineSpace.zeroSection (ULift.{u} (Fin 1)) U) hb).symm
    · intro i
      let A : (pullback h h).AffineZariskiSite := ⟨⊤, isAffineOpen_top _⟩
      let j := reesConeChart a A
      have : IsOpenImmersion j := by
        dsimp only [j, reesConeChart]
        infer_instance
      have hjiso : IsIso j := by
        apply isIso_of_isOpenImmersion_of_opensRange_eq_top
        dsimp only [j, reesConeChart]
        rw [← Scheme.AffineZariskiSite.toBase_preimage]
        exact Scheme.Hom.preimage_top _
      apply (ConcreteCategory.bijective_of_isIso j.appTop).1
      change (j ≫ a.ker.normalConeToDeformationSpace ≫ G).appTop _ =
        (j ≫ q.hom ≫ N.normal.hom ≫ AffineSpace.map I
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) U)).appTop _
      have hjzero : j ≫ a.ker.normalConeToDeformationSpace =
          Spec.map ((Scheme.toQuotientPresheaf a.ker.tIdeal a.ker.map_tIdeal).app (op A)) ≫
            colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
              a.ker.coequifibered_toReesPresheaf).functor A :=
        Scheme.AffineZariskiSite.ι_relativeGluingMap _ _ _ A
      rw [← Category.assoc j a.ker.normalConeToDeformationSpace G, hjzero, Category.assoc]
      obtain ⟨hi, hv⟩ := pair_coordinate I a D wg A i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      have hvG : (colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
          a.ker.coequifibered_toReesPresheaf).functor A ≫ G).appTop
            (AffineSpace.coord (AffineSpace (ULift.{u} (Fin 1)) U) i) = _ := hv
      refine (congrArg (fun y ↦
        (Spec.map ((Scheme.toQuotientPresheaf a.ker.tIdeal a.ker.map_tIdeal).app
          (op A))).appTop y) hvG).trans ?_
      erw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      erw [AffineSpace.map_appTop_coord
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) U) i]
      have hn := normal_coordinate_top N i.down
      obtain ⟨b, hb, hsN⟩ := N.sign (c.appTop (AffineSpace.coord V i))
      have hinv : N.conormal.inv.val.app (op ⊤)
          (h.relativeDifferentialsDerivation.d (X := op ⊤)
            (c.appTop (AffineSpace.coord V i))) =
          ConormalGradedAlgebra.representative a 1 ⊤ b := by
        have hsN' : N.conormal.hom.val.app (op ⊤)
            (ConormalGradedAlgebra.representative a 1 ⊤ b) =
              h.relativeDifferentialsDerivation.d (X := op ⊤)
                (c.appTop (AffineSpace.coord V i)) := by simpa using hsN
        rw [← hsN']
        exact congrArg (fun t ↦ t.val.app (op ⊤)
          (ConormalGradedAlgebra.representative a 1 ⊤ b)) N.conormal.hom_inv_id
      rw [hinv] at hn
      erw [hn]
      have hbmem : (ConormalGradedAlgebra.powerInclusion a 1).val.app (op ⊤) b ∈
          a.ker.siteIdeal A := by
        obtain ⟨hbmem, _⟩ := ((ConormalGradedAlgebra.presentation a).affineChart
          ⟨⊤, isAffineOpen_top _⟩).choose_spec 1 b
        simpa only [pow_one] using hbmem
      have hnorm := hq.2.2 A b hbmem (by
        change ⊤ ≤ (reesConeChart (pullback.diagonal h) A ≫ q.hom) ⁻¹ᵁ ⊤
        simp)
      have hnorm' : (j ≫ q.hom).appTop
          ((coneAlgebraIso a).hom.right.hom.app (op ⊤)
            (((ConormalGradedAlgebra.presentation a).inclusion 1).val.app (op ⊤)
              (ConormalGradedAlgebra.representative a 1 ⊤ b))) =
          (Scheme.ΓSpecIso (a.ker.normalConePresheaf.obj (op A))).inv
            (Ideal.Quotient.mk _ ⟨LaurentPolynomial.C (R := Γ((pullback h h : Scheme.{u}), ⊤))
              ((ConormalGradedAlgebra.powerInclusion a 1).val.app (op ⊤) b) *
                LaurentPolynomial.T (-1),
              Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra hbmem⟩) := by
        simpa only [A, Scheme.Hom.preimage_top, Scheme.Hom.appLE_top_top,
          ConormalGradedAlgebra.homogeneousClass] using hnorm
      have hnorm'' := hnorm'
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hnorm''
      refine Eq.trans ?_ hnorm''.symm
      congr 1
      congr 1
      apply Subtype.ext
      change LaurentPolynomial.C (D.appLE ⊤ ⊤ (by simp) (AffineSpace.coord U i)) *
        LaurentPolynomial.T (-1) = _
      change LaurentPolynomial.C (D.appLE ⊤ ⊤ (by simp) (AffineSpace.coord U i)) *
        LaurentPolynomial.T (-1) = LaurentPolynomial.C (R := Γ((pullback h h : Scheme.{u}), ⊤))
          ((ConormalGradedAlgebra.powerInclusion a 1).val.app (op ⊤) b) *
            LaurentPolynomial.T (-1)
      rw [Scheme.Hom.appLE_top_top, AffineSpace.homOfVector_appTop_coord]
      exact congrArg (fun y : Γ((pullback h h : Scheme.{u}), ⊤) ↦
        LaurentPolynomial.C y * LaurentPolynomial.T (-1)) hb.symm
  · intro A hA
    let j₀ := colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
      a.ker.coequifibered_toReesPresheaf).functor A
    have hjR : Set.range j₀ ⊆ Set.range R.ι := by
      rw [Scheme.Opens.range_ι]
      have hr := (Scheme.AffineZariskiSite.relativeGluingData
        a.ker.coequifibered_toReesPresheaf).preimage_toBase_eq_range_ι A
      change Set.range j₀ ⊆ a.ker.deformationSpaceProj ⁻¹' (O : Set ↥(pullback h h : Scheme.{u}))
      rw [← hr]
      rintro t ht
      apply hA
      change t ∈ a.ker.deformationSpaceProj ⁻¹' Set.range A.1.ι at ht
      rw [Scheme.Opens.range_ι] at ht
      exact ht
    let j := IsOpenImmersion.lift R.ι j₀ hjR
    have hj : j ≫ R.ι = j₀ := IsOpenImmersion.lift_fac ..
    refine ⟨j, hj, ?_, fun i ↦ ?_⟩
    · change (j ≫ f ≫ _).appTop _ = _
      rw [Category.assoc, hGo, ← Category.assoc, hj]
      exact parameter_coordinate p a A
    · obtain ⟨hi, hv⟩ := pair_coordinate I a D wg A i
      have hcoord : D.appLE ⊤ A.1 (by simp) (AffineSpace.coord U i) =
          (pullback h h).presheaf.map (homOfLE le_top).op
            ((pullback.snd h h).appTop (c.appTop (AffineSpace.coord V i)) -
              p.appTop (c.appTop (AffineSpace.coord V i))) := by
        rw [← Scheme.Hom.appLE_map (e := by simp), Scheme.Hom.appLE_top_top,
          CommRingCat.comp_apply, AffineSpace.homOfVector_appTop_coord]
      refine ⟨hcoord ▸ hi, ?_⟩
      change (j ≫ R.ι ≫ G).appTop _ = _
      rw [← Category.assoc, hj]
      convert! hv using 1
      congr 1
      apply Subtype.ext
      exact congrArg (fun t ↦ LaurentPolynomial.C t * LaurentPolynomial.T (-1)) hcoord.symm
  · intro hd
    subst d
    have : IsIso (AffineSpace.zeroSection (ULift.{u} (Fin 0)) U) :=
      by
        have : IsIso (AffineSpace.zeroSection (ULift.{u} (Fin 0)) U ≫
            (AffineSpace (ULift.{u} (Fin 0)) U ↘ U)) := by
          rw [AffineSpace.zeroSection_over]
          infer_instance
        exact IsIso.of_isIso_comp_right _ (AffineSpace (ULift.{u} (Fin 0)) U ↘ U)
    exact H.isIso_fst_of_isIso
  · intro hd
    subst d
    have hziso : IsIso (AffineSpace.zeroSection (ULift.{u} (Fin 0)) U) := by
      have : IsIso (AffineSpace.zeroSection (ULift.{u} (Fin 0)) U ≫
          (AffineSpace (ULift.{u} (Fin 0)) U ↘ U)) := by
        rw [AffineSpace.zeroSection_over]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (AffineSpace (ULift.{u} (Fin 0)) U ↘ U)
    have hsiso : IsIso s := H.isIso_fst_of_isIso
    have heiso : IsIso (O.ι ≫ D) := by
      have : IsIso (s ≫ (O.ι ≫ D)) := by rw [w]; infer_instance
      exact IsIso.of_isIso_comp_left s (O.ι ≫ D)
    have hφiso : IsIso φ := hφpb.isIso_fst_of_isIso
    have hFiso : IsIso F := inferInstance
    have : IsIso (m.hom ≫ f) := hmf.symm ▸ hFiso
    exact IsIso.of_isIso_comp_left m.hom f



end AlgebraicGeometry.DiagonalDifferenceReesFrame
