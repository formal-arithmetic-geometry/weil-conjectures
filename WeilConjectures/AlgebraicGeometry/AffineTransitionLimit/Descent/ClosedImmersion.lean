/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.DescendsToStage
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Closed immersions descend to a finite stage

A finitely presented morphism whose base change to a cofiltered limit is a closed immersion is a
closed immersion at a finite stage
(`AlgebraicGeometry.Scheme.exists_isClosedImmersion_overPullbackMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section FinitePresentationDescent
section Descent

set_option backward.defeqAttrib.useBackward true
variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- **A finitely presented closed subscheme of the limit is closed at a finite stage.**

Let `{Dⱼ}` be a cofiltered inverse system of schemes with affine transition maps, let
`q : Z ⟶ D_k` be a morphism of finite presentation to a quasi-compact stage and let
`X = Z ×_{D_k} lim Dⱼ` be its base change to the limit. If `X ⟶ lim Dⱼ` is a closed
immersion, then the base change of `q` to some later stage `k' ⟶ k`, and to every stage
after that, is a closed immersion. -/
lemma Scheme.exists_isClosedImmersion_pullback_snd {k : I} [CompactSpace (D.obj k)]
    {Z : Scheme.{u}} {q : Z ⟶ D.obj k}
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    {X : Scheme.{u}} {w : X ⟶ c.pt} [IsClosedImmersion w]
    {h : X ⟶ Z} (H : IsPullback h w q (c.π.app k)) :
    ∃ (k' : I) (f : k' ⟶ k), ∀ {k'' : I} (f' : k'' ⟶ k'),
      IsClosedImmersion (pullback.snd q (D.map (f' ≫ f))) := by
  classical
  have : LocallyOfFinitePresentation w := MorphismProperty.of_isPullback H inferInstance
  set 𝒰 := (D.obj k).affineCover.finiteSubcover with h𝒰
  -- For every affine chart of the base stage, the canonical chart-restricted model of `Z`
  -- becomes a closed immersion at some later stage.
  have key : ∀ a : 𝒰.I₀, ∃ ja : Over k,
      IsClosedImmersion (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) := by
    intro a
    -- The system base changed to the chart has affine stages.
    have : ∀ j : Over k, IsAffine ((baseChangeDiagram D (𝒰.f a)).obj j) := fun j ↦
      inferInstanceAs (IsAffine (pullback (𝒰.f a) (D.map j.hom)))
    -- The base change of `w` to the chart-restricted limit is a finitely presented closed
    -- immersion.
    obtain ⟨wA, hwsq⟩ : ∃ wA : pullback (𝒰.f a) (h ≫ q) ⟶
          (baseChangeCone D c (𝒰.f a)).pt,
        IsPullback wA (pullback.snd (𝒰.f a) (h ≫ q))
          (pullback.snd (𝒰.f a) (c.π.app k)) w :=
      ⟨_, isPullback_pullback_map (𝒰.f a) (h ≫ q) (c.π.app k) w H.w.symm⟩
    have hwA₁ : IsClosedImmersion wA :=
      MorphismProperty.of_isPullback hwsq.flip ‹IsClosedImmersion w›
    have hwA₂ : LocallyOfFinitePresentation wA :=
      MorphismProperty.of_isPullback hwsq.flip ‹LocallyOfFinitePresentation w›
    -- Apply the affine case to obtain a closed immersion model at a stage `ja`.
    obtain ⟨ja, Ya, hYaff, pa, hpa, hpac, ha, Ha⟩ :=
      Scheme.exists_isPullback_of_isClosedImmersion_of_isAffine
        (baseChangeDiagram D (𝒰.f a)) (baseChangeCone D c (𝒰.f a))
        (isLimitBaseChangeCone D c (𝒰.f a) hc) wA
    -- The canonical chart model of `Z` at the stage `ja` is a second finite-stage model.
    have hbot : (baseChangeCone D c (𝒰.f a)).π.app ja ≫
        (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a) =
        pullback.snd (𝒰.f a) (c.π.app k) ≫ c.π.app k := by
      rw [← Category.assoc, baseChangeCone_π_app_fst]
      exact pullback.condition
    have BIG : IsPullback (pullback.snd (𝒰.f a) (h ≫ q) ≫ h) wA q
        ((baseChangeCone D c (𝒰.f a)).π.app ja ≫
          (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      (hwsq.flip.paste_horiz H).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp) (by simpa using hbot.symm)
    have hMsq := BIG.of_right'
      (IsPullback.of_hasPullback q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
    -- Instances for the comparison of the two models.
    have := hYaff
    have := hpa
    have : CompactSpace Ya := inferInstance
    have : QuasiSeparatedSpace Ya := inferInstance
    have : QuasiCompact (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ ‹QuasiCompact q›
    have : QuasiSeparated (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      MorphismProperty.pullback_snd (P := @QuasiSeparated) _ _ ‹QuasiSeparated q›
    have : LocallyOfFinitePresentation
        (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _
        ‹LocallyOfFinitePresentation q›
    have : @LocallyOfFinitePresentation
        (pullback q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
        ((baseChangeDiagram D (𝒰.f a)).obj ja)
        (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) := ‹_›
    have : CompactSpace ↥(pullback q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      QuasiCompact.compactSpace_of_compactSpace
        (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
    have : QuasiSeparatedSpace ↥(pullback q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a)) :=
      quasiSeparatedSpace_of_quasiSeparated
        (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
    -- The two models agree at a later stage `ka`, so the chart model becomes closed there.
    obtain ⟨ka, fa, tail⟩ :=
      exists_iso_of_isPullback (isLimitBaseChangeCone D c (𝒰.f a) hc) Ha hMsq
    obtain ⟨e, he₁, -⟩ := tail
      (IsPullback.of_hasPullback pa ((baseChangeDiagram D (𝒰.f a)).map fa))
      (isPullbackLift_fst fa Ha) (isPullbackLift_snd fa Ha)
      (IsPullback.of_hasPullback (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
        ((baseChangeDiagram D (𝒰.f a)).map fa))
      (isPullbackLift_fst fa hMsq) (isPullbackLift_snd fa hMsq)
    have hclosed₁ :
        IsClosedImmersion (pullback.snd pa ((baseChangeDiagram D (𝒰.f a)).map fa)) :=
      MorphismProperty.pullback_snd _ _ hpac
    have hclosed₂ : IsClosedImmersion
        (pullback.snd (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
          ((baseChangeDiagram D (𝒰.f a)).map fa)) := by
      rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion e.hom, he₁]
      exact hclosed₁
    -- Identify the further base change with the canonical chart model at the stage `ka`.
    have hpaste : IsPullback
        (pullback.fst (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
            ((baseChangeDiagram D (𝒰.f a)).map fa :
              pullback (𝒰.f a) (D.map ka.hom) ⟶ pullback (𝒰.f a) (D.map ja.hom)) ≫
          pullback.fst q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
        (pullback.snd (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
          ((baseChangeDiagram D (𝒰.f a)).map fa :
            pullback (𝒰.f a) (D.map ka.hom) ⟶ pullback (𝒰.f a) (D.map ja.hom)))
        q (pullback.fst (𝒰.f a) (D.map ka.hom) ≫ 𝒰.f a) := by
      have h1 := (IsPullback.of_hasPullback
          (pullback.snd q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
          ((baseChangeDiagram D (𝒰.f a)).map fa :
            pullback (𝒰.f a) (D.map ka.hom) ⟶ pullback (𝒰.f a) (D.map ja.hom))).paste_horiz
        (IsPullback.of_hasPullback q (pullback.fst (𝒰.f a) (D.map ja.hom) ≫ 𝒰.f a))
      exact h1.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp)
    have hχ := IsPullback.of_hasPullback q (pullback.fst (𝒰.f a) (D.map ka.hom) ≫ 𝒰.f a)
    refine ⟨ka, (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (Arrow.isoMk (hpaste.isoIsPullback _ _ hχ) (Iso.refl _)
        (by simp))).mp hclosed₂⟩
  -- Choose a stage below the finitely many chart stages.
  choose ja hja using key
  obtain ⟨jstar, hjstar⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image ja)
  refine ⟨jstar.left, jstar.hom, ?_⟩
  intro k'' f'
  -- It suffices to prove the claim at the stage `jstar` itself.
  have hlater : IsClosedImmersion (pullback.snd q (D.map jstar.hom)) →
      IsClosedImmersion (pullback.snd q (D.map (f' ≫ jstar.hom))) := fun hj ↦
    MorphismProperty.of_isPullback
      (isPullback_pullback_map q (D.map (f' ≫ jstar.hom)) (D.map jstar.hom) (D.map f')
        (by rw [← D.map_comp])) hj
  apply hlater
  -- The chart models at the stage `jstar` are closed immersions.
  have hstage : ∀ a : 𝒰.I₀,
      IsClosedImmersion (pullback.snd q (pullback.fst (𝒰.f a) (D.map jstar.hom) ≫ 𝒰.f a)) := by
    intro a
    obtain ⟨g⟩ := hjstar (Finset.mem_image_of_mem ja (Finset.mem_univ a))
    have hsq := isPullback_pullback_map q
      (pullback.fst (𝒰.f a) (D.map jstar.hom) ≫ 𝒰.f a)
      (pullback.fst (𝒰.f a) (D.map (ja a).hom) ≫ 𝒰.f a)
      ((baseChangeDiagram D (𝒰.f a)).map g)
      (baseChangeDiagram_map_fst_assoc D (𝒰.f a) g (𝒰.f a))
    exact MorphismProperty.of_isPullback hsq (hja a)
  -- Glue: being a closed immersion is local on the target.
  refine IsZariskiLocalAtTarget.of_openCover (𝒰.pullback₁ (D.map jstar.hom)) ?_
  intro a
  -- The piece of the pulled-back cover is the canonical chart model at `jstar`.
  have h1 := (IsPullback.of_hasPullback (pullback.snd q (D.map jstar.hom))
      ((𝒰.pullback₁ (D.map jstar.hom)).f a)).paste_horiz
    (IsPullback.of_hasPullback q (D.map jstar.hom))
  have h2 : IsPullback
      (pullback.fst (pullback.snd q (D.map jstar.hom)) ((𝒰.pullback₁ (D.map jstar.hom)).f a) ≫
        pullback.fst q (D.map jstar.hom))
      (Scheme.Cover.pullbackHom (𝒰.pullback₁ (D.map jstar.hom))
          (pullback.snd q (D.map jstar.hom)) a ≫
        (pullbackSymmetry (D.map jstar.hom) (𝒰.f a)).hom)
      q (pullback.fst (𝒰.f a) (D.map jstar.hom) ≫ 𝒰.f a) := by
    refine h1.of_iso (Iso.refl _) (Iso.refl _)
      (pullbackSymmetry (D.map jstar.hom) (𝒰.f a)) (Iso.refl _) (by simp) ?_ (by simp) ?_
    · simp [Scheme.Cover.pullbackHom]
    · simp [pullback.condition]
  have hχ := IsPullback.of_hasPullback q (pullback.fst (𝒰.f a) (D.map jstar.hom) ≫ 𝒰.f a)
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk (h2.isoIsPullback _ _ hχ) (pullbackSymmetry (D.map jstar.hom) (𝒰.f a))
      (IsPullback.isoIsPullback_hom_snd _ _ h2 hχ))).mpr (hstage a)

include hc in
/-- **A finitely presented morphism whose base change to the limit is a closed immersion is a
closed immersion at a finite stage.**

Let `γ` be a morphism of finite presentation between schemes over a stage `D_k`, with
quasi-compact quasi-separated target. If the base change of `γ` to the limit `lim Dⱼ` is a
closed immersion, then so is its base change to some stage `k' ⟶ k` and to every stage after
that. (Blueprint: `lemma:nagata-closed-immersion-stage-exists`.) -/
lemma Scheme.exists_isClosedImmersion_overPullbackMap {k : I}
    {Z Y : Over (D.obj k)} (γ : Z ⟶ Y)
    [LocallyOfFinitePresentation γ.left] [QuasiCompact γ.left] [QuasiSeparated γ.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    (hS : IsClosedImmersion ((Over.pullback (c.π.app k)).map γ).left) :
    ∃ (k' : I) (f : k' ⟶ k), ∀ {k'' : I} (f' : k'' ⟶ k'),
      IsClosedImmersion ((Over.pullback (D.map (f' ≫ f))).map γ).left := by
  classical
  -- The identity-stage model of `γ` over the system base changed to `Y`.
  have hw : γ.left ≫ Y.hom = Z.hom ≫ D.map (𝟙 k) := by
    rw [Over.w γ, D.map_id, Category.comp_id]
  have he : (𝟙 Y.left) ≫ Y.hom = Y.hom ≫ D.map (𝟙 k) := by
    rw [Category.id_comp, D.map_id, Category.comp_id]
  have : IsIso (D.map (𝟙 k)) := by rw [D.map_id]; infer_instance
  have hfst : IsIso (pullback.fst Y.hom (D.map (𝟙 k))) := inferInstance
  have hfl : pullback.fst Y.hom (D.map (𝟙 k)) ≫ pullback.lift (𝟙 Y.left) Y.hom he = 𝟙 _ := by
    apply pullback.hom_ext
    · simp
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition, D.map_id,
        Category.comp_id]
  have he₀ : IsIso (pullback.lift (𝟙 Y.left) Y.hom he) := by
    rw [show pullback.lift (𝟙 Y.left) Y.hom he = inv (pullback.fst Y.hom (D.map (𝟙 k))) from
      IsIso.eq_inv_of_hom_inv_id hfl]
    infer_instance
  have hq₀ : pullback.lift γ.left Z.hom hw = γ.left ≫ pullback.lift (𝟙 Y.left) Y.hom he := by
    apply pullback.hom_ext <;> simp
  have : LocallyOfFinitePresentation (pullback.lift γ.left Z.hom hw) := by
    rw [hq₀]; infer_instance
  have : QuasiCompact (pullback.lift γ.left Z.hom hw) := by rw [hq₀]; infer_instance
  have : QuasiSeparated (pullback.lift γ.left Z.hom hw) := by rw [hq₀]; infer_instance
  -- The base change of `γ` to the limit is the base change of the identity-stage model.
  have hsq : IsPullback (pullback.fst Z.hom (c.π.app k))
      ((Over.pullback (c.π.app k)).map γ).left (pullback.lift γ.left Z.hom hw)
      ((baseChangeCone D c Y.hom).π.app (Over.mk (𝟙 k))) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_baseChangeCone_π D c Y.hom (Over.mk (𝟙 k)))
    · refine (IsPullback.of_hasPullback Z.hom (c.π.app k)).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback])
        (by simp) (by simp)
    · apply pullback.hom_ext <;>
        simp [Over.pullback,
          pullback.condition]
  have hI1 : @LocallyOfFinitePresentation Z.left
      ((baseChangeDiagram D Y.hom).obj (Over.mk (𝟙 k))) (pullback.lift γ.left Z.hom hw) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.lift γ.left Z.hom hw))
  have hI2 : @QuasiCompact Z.left
      ((baseChangeDiagram D Y.hom).obj (Over.mk (𝟙 k))) (pullback.lift γ.left Z.hom hw) :=
    inferInstanceAs (QuasiCompact (pullback.lift γ.left Z.hom hw))
  have hI3 : @QuasiSeparated Z.left
      ((baseChangeDiagram D Y.hom).obj (Over.mk (𝟙 k))) (pullback.lift γ.left Z.hom hw) :=
    inferInstanceAs (QuasiSeparated (pullback.lift γ.left Z.hom hw))
  have hI4 : @IsClosedImmersion (pullback Z.hom (c.π.app k)) (baseChangeCone D c Y.hom).pt
      ((Over.pullback (c.π.app k)).map γ).left := hS
  obtain ⟨k', fA, tail⟩ :=
    @Scheme.exists_isClosedImmersion_pullback_snd (Over k) _ (baseChangeDiagram D Y.hom)
      (baseChangeCone D c Y.hom) (isLimitBaseChangeCone D c Y.hom hc) _ _
      (Over.mk (𝟙 k)) inferInstance
      Z.left (pullback.lift γ.left Z.hom hw) hI1 hI2 hI3
      (pullback Z.hom (c.π.app k)) ((Over.pullback (c.π.app k)).map γ).left hI4
      (pullback.fst Z.hom (c.π.app k)) hsq
  refine ⟨k'.left, k'.hom, ?_⟩
  intro k'' f'
  have htail := tail (Over.homMk f' : Over.mk (f' ≫ k'.hom) ⟶ k')
  -- Both the resulting closed immersion and the base change of `γ` to the stage `k''` are
  -- pullbacks of `γ.left` along the projection of the stage model of `Y`.
  have hργ : IsPullback (pullback.fst Z.hom (D.map (f' ≫ k'.hom)))
      ((Over.pullback (D.map (f' ≫ k'.hom))).map γ).left γ.left
      (pullback.fst Y.hom (D.map (f' ≫ k'.hom))) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback Y.hom (D.map (f' ≫ k'.hom)))
    · refine (IsPullback.of_hasPullback Z.hom (D.map (f' ≫ k'.hom))).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback])
        (by simp) (by simp)
    · simp [Over.pullback]
  have hsq3 : IsPullback (𝟙 Z.left) (pullback.lift γ.left Z.hom hw) γ.left
      (pullback.fst Y.hom (D.map (𝟙 k))) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, pullback.lift_fst]⟩
  have hρq : IsPullback
      (pullback.fst (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map (Over.homMk f' ≫ fA : Over.mk (f' ≫ k'.hom) ⟶ _)))
      (pullback.snd (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map (Over.homMk f' ≫ fA : Over.mk (f' ≫ k'.hom) ⟶ _)))
      γ.left (pullback.fst Y.hom (D.map (f' ≫ k'.hom))) := by
    have h1 := (IsPullback.of_hasPullback (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map
          (Over.homMk f' ≫ fA : Over.mk (f' ≫ k'.hom) ⟶ _))).paste_horiz hsq3
    exact h1.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk (hρq.isoIsPullback _ _ hργ) (Iso.refl _)
      (by simp))).mp htail

end Descent

end FinitePresentationDescent

end AlgebraicGeometry
