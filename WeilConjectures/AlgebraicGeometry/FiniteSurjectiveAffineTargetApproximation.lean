/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed
import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FinitePresentationApproximation
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Noetherian factor for a finite surjective affine morphism

This packages the approximation and descent part of the proof of Stacks Lemma 01ZT.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The finite surjective affine stage obtained by Noetherian approximation. -/
structure NoetherianAffineFactor {X Y : Scheme.{u}} (f : X ⟶ Y) where
  Z : Scheme.{u}
  q : Y ⟶ Z
  W : Scheme.{u}
  g : W ⟶ Z
  affine_q : IsAffineHom q
  noetherian_Z : AlgebraicGeometry.IsNoetherian Z
  finite_g : IsFinite g
  surjective_g : Surjective g
  affine_W : IsAffine W

-- The base change of a map to the Limits.terminal object of `Over S` has the same
-- properties as the usual second pullback projection, up to a target isomorphism.
private theorem property_over_pullback_terminal
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S T A : Scheme.{u}} (p : A ⟶ S) (q : T ⟶ S) :
    P (((Over.pullback q).map (Over.homMk p (by simp) :
      Over.mk p ⟶ Over.mk (𝟙 S))).left) ↔ P (Limits.pullback.snd p q) := by
  have he : (((Over.pullback q).map (Over.homMk p (by simp) :
      Over.mk p ⟶ Over.mk (𝟙 S))).left) ≫ Limits.pullback.snd (𝟙 S) q =
      Limits.pullback.snd p q := by
    simp
  rw [← he]
  exact (MorphismProperty.cancel_right_of_respectsIso P _ _).symm

-- Stacks 01ZT, approximation paragraphs after the reduction to finite presentation.
private theorem factor_of_finitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] [IsAffine X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [LocallyOfFinitePresentation f] :
    Nonempty (NoetherianAffineFactor f) := by
  classical
  -- Reindex absolute Noetherian approximation by a nonempty directed order.
  obtain ⟨N⟩ := Y.nonempty_noetherianApproximation
  obtain ⟨I, horder, hdir, hne, F, hfinal⟩ := IsFiltered.exists_directed N.Iᵒᵖ
  let := horder
  let := hdir
  let := hne
  let := hfinal
  let R := F.leftOp
  let D := R ⋙ N.D
  let c := (Limits.Cone.mk Y N.π).whisker R
  have hc : Limits.IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv R (Limits.Cone.mk Y N.π)).symm N.isLimit
  let (i : Iᵒᵖ) : CompactSpace (D.obj i) := N.compactSpace_obj (R.obj i)
  let (i : Iᵒᵖ) : QuasiSeparatedSpace (D.obj i) := by
    change QuasiSeparatedSpace (N.D.obj (R.obj i))
    infer_instance
  let {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom (D.map a) := N.isAffineHom_map (R.map a)
  -- Spread out the finitely presented morphism and transport its limit properties.
  obtain ⟨i₀, A, p, hp, hqc, hqs, a, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation (D := D) (c := c) hc f
  let := hp
  let := hqc
  let := hqs
  let : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace p
  let : QuasiSeparatedSpace A := quasiSeparatedSpace_of_quasiSeparated p
  have hfinite : IsFinite (Limits.pullback.snd p (c.π.app i₀)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite H.isoPullback.hom,
      H.isoPullback_hom_snd]
    infer_instance
  have hsurj : Surjective (Limits.pullback.snd p (c.π.app i₀)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Surjective H.isoPullback.hom,
      H.isoPullback_hom_snd]
    infer_instance
  -- The descent lemmas use morphisms in `Over`; the target is its Limits.terminal object.
  let X₀ := Over.mk p
  let Y₀ := Over.mk (𝟙 (D.obj i₀))
  let f₀ : X₀ ⟶ Y₀ := Over.homMk p (by simp [X₀, Y₀])
  let : CompactSpace X₀.left := ‹CompactSpace A›
  let : QuasiSeparatedSpace X₀.left := ‹QuasiSeparatedSpace A›
  let : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i₀))
  let : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i₀))
  let : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType p)
  let : LocallyOfFinitePresentation f₀.left := hp
  have hfinite' : IsFinite (((Over.pullback (c.π.app i₀)).map f₀).left) :=
    (property_over_pullback_terminal @IsFinite p (c.π.app i₀)).mpr hfinite
  have hsurj' : Surjective (((Over.pullback (c.π.app i₀)).map f₀).left) :=
    (property_over_pullback_terminal @Surjective p (c.π.app i₀)).mpr hsurj
  obtain ⟨i₁, hi₁, hf₁⟩ :=
    exists_isFinite_baseChange_stage D c hc i₀.unop X₀ Y₀ f₀ hfinite'
  obtain ⟨i₂, hi₂, hs₂⟩ :=
    exists_surjective_of_isLimit D c hc i₀.unop X₀ Y₀ f₀ hsurj'
  have hf₁' : IsFinite (Limits.pullback.snd p (D.map (homOfLE hi₁).op)) :=
    (property_over_pullback_terminal @IsFinite p _).mp hf₁
  have hs₂' : Surjective (Limits.pullback.snd p (D.map (homOfLE hi₂).op)) :=
    (property_over_pullback_terminal @Surjective p _).mp hs₂
  -- The source models form a limit diagram over the cofinal category of later stages.
  let B := baseChangeDiagram D p
  let bc := baseChangeCone D c p
  have hbc : Limits.IsLimit bc := isLimitBaseChangeCone D c p hc
  let : IsAffine bc.pt := (IsAffine.iff_of_isIso H.isoPullback.hom).mp inferInstance
  let (j : Over i₀) : CompactSpace (B.obj j) := by
    change CompactSpace ↥(Limits.pullback p (D.map j.hom) : Scheme.{u})
    exact QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.snd p (D.map j.hom))
  let (j : Over i₀) : QuasiSeparatedSpace (B.obj j) := by
    change QuasiSeparatedSpace ↥(Limits.pullback p (D.map j.hom) : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd p (D.map j.hom))
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit B bc hbc
  -- One common upper bound preserves all three stage properties by base change.
  obtain ⟨k₁, hk₁₁, hk₁₂⟩ := exists_ge_ge i₁ i₂
  obtain ⟨k, hkk₁, hkj⟩ := exists_ge_ge k₁ j.left.unop
  have hk₁ := hk₁₁.trans hkk₁
  have hk₂ := hk₁₂.trans hkk₁
  let l : Over i₀ := Over.mk (homOfLE (hi₁.trans hk₁)).op
  let l₁ : Over i₀ := Over.mk (homOfLE hi₁).op
  let l₂ : Over i₀ := Over.mk (homOfLE hi₂).op
  let b₁ : l ⟶ l₁ := Over.homMk (homOfLE hk₁).op (by subsingleton)
  let b₂ : l ⟶ l₂ := Over.homMk (homOfLE hk₂).op (by subsingleton)
  let b₃ : l ⟶ j := Over.homMk (homOfLE hkj).op (by subsingleton)
  have hfk : IsFinite (Limits.pullback.snd p (D.map l.hom)) :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (isPullback_baseChangeDiagram_map D p b₁) hf₁'
  have hsk : Surjective (Limits.pullback.snd p (D.map l.hom)) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_baseChangeDiagram_map D p b₂) hs₂'
  let := hj
  let : IsAffine (B.obj l) := isAffine_of_isAffineHom (B.map b₃)
  exact ⟨{
    Z := D.obj l.left
    q := c.π.app l.left
    W := B.obj l
    g := Limits.pullback.snd p (D.map l.hom)
    affine_q := isAffineHom_π_app D c hc l.left
    noetherian_Z := N.isNoetherian_obj (R.obj l.left)
    finite_g := hfk
    surjective_g := hsk
    affine_W := inferInstance }⟩

/-- A finite surjective map from an affine scheme admits a Noetherian affine stage. -/
theorem exists_noetherian_affine_factor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] [IsAffine X] :
    Nonempty (NoetherianAffineFactor f) := by
  classical
  let : CompactSpace Y := ⟨by
    rw [← (Surjective.surj (f := f)).range_eq]
    exact isCompact_range f.continuous⟩
  let : IsSeparated (Limits.terminal.from Y) :=
    isSeparated_of_surjective_universallyClosed (Limits.terminal.from X) (Limits.terminal.from Y)
      f (Limits.terminal.comp_from f)
  let : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Limits.terminal.from Y)
  obtain ⟨F, hF⟩ := f.exists_finiteApproximation_of_isIntegralHom
  obtain ⟨i, hi⟩ := Scheme.exists_isAffine_of_isLimit F.D (Limits.Cone.mk X F.π) F.isLimit
  let := hi
  let := hF i
  let : Surjective (F.p i) := ⟨by
    have hsurj : Function.Surjective (F.π.app i ≫ F.p i) := by
      rw [F.π_p]
      exact Surjective.surj
    exact Function.Surjective.of_comp hsurj⟩
  obtain ⟨A⟩ := factor_of_finitePresentation (F.p i)
  exact ⟨{
    Z := A.Z
    q := A.q
    W := A.W
    g := A.g
    affine_q := A.affine_q
    noetherian_Z := A.noetherian_Z
    finite_g := A.finite_g
    surjective_g := A.surjective_g
    affine_W := A.affine_W }⟩

end AlgebraicGeometry
