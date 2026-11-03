/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingBundleSectionOrientationData

import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionComparisonIsoPasting
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceCompactComparisonRestriction
import all Mathlib.Logic.Small.Defs

/-! # Local normalization of the identity-adjunction comparison in rank zero -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

attribute [local irreducible] rightDerivedLowerShriek rightDerivedUpperShriek upperStar
  unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekId
  leftDerivedUpperStarId leftDerivedUpperStarComp
  HasDerivedCategory.ofIsGrothendieckAbelian
  rightDerivedLowerShriekBaseChangeMap
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor

-- These local reductions identify the zero-stage schemes and their module categories.
set_option allowUnsafeReducibility true in
attribute [local reducible] Scheme.Modules affineTraceTower affineTraceProjection
  affineLinearBaseCoefficient bundleSectionObject bundleSectionOmega
attribute [local implicit_reducible] bundleSectionChartZero

private lemma iso_id_map {C : Type*} [Category C] {F : C ⥤ C}
    (e : F ≅ 𝟭 C) (K : C) : e.hom.app (F.obj K) = F.map (e.hom.app K) := by
  apply (cancel_mono (e.hom.app K)).mp
  exact (e.hom.naturality (e.hom.app K)).symm

set_option maxHeartbeats 1600000 in
-- The exchange composition equation carries several large derived-functor instances.
private lemma identity_exchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S] (f : T ⟶ S)
    (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
        ((unboundedEtaleLowerShriekId A S).inv.app K) ≫
      (unboundedEtaleCompactSupportBaseChange A (IsPullback.id_vert f)).app K =
    (unboundedEtaleLowerShriekId A T).inv.app
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K) := by
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 S)
  let G := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T)
  let P := (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  let C := unboundedEtaleCompactSupportBaseChange A (IsPullback.id_vert f)
  have : IsIso C := (unboundedEtaleCompactSupport_baseChange A (IsPullback.id_vert f)).1
  have : G.Faithful := Functor.Faithful.of_iso (unboundedEtaleLowerShriekId A T).symm
  have h := congr_app (unboundedEtaleCompactSupport_baseChange_composition A
    (IsPullback.id_vert f) (IsPullback.id_vert f)
    (IsPullback.id_vert f)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp] at h
  have hs := congr_app (unboundedEtaleLowerShriekCompIso_units A (𝟙 S)).2 K
  have ht := congr_app (unboundedEtaleLowerShriekCompIso_units A (𝟙 T)).2 (P.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, unboundedEtaleLowerShriekCongr,
    Iso.refl_hom, Category.comp_id] at hs ht
  rw [iso_id_map (unboundedEtaleLowerShriekId A S) K] at hs
  rw [iso_id_map (unboundedEtaleLowerShriekId A T) (P.obj K)] at ht
  change (unboundedEtaleLowerShriekCompIso A (𝟙 S) (𝟙 S)).hom.app K =
    F.map ((unboundedEtaleLowerShriekId A S).hom.app K) ≫ 𝟙 _ at hs
  change (unboundedEtaleLowerShriekCompIso A (𝟙 T) (𝟙 T)).hom.app (P.obj K) =
    G.map ((unboundedEtaleLowerShriekId A T).hom.app (P.obj K)) ≫ 𝟙 _ at ht
  simp only [Category.comp_id] at hs ht
  rw [hs, ht] at h
  have hn := C.naturality ((unboundedEtaleLowerShriekId A S).hom.app K)
  simp only [Functor.comp_map] at hn
  erw [hn] at h
  have he : P.map ((unboundedEtaleLowerShriekId A S).hom.app K) =
      C.app K ≫ (unboundedEtaleLowerShriekId A T).hom.app (P.obj K) := by
    apply G.map_injective
    simpa only [Functor.map_comp] using (cancel_epi (C.app (F.obj K))).mp h
  apply (cancel_mono ((unboundedEtaleLowerShriekId A T).hom.app (P.obj K))).mp
  simp only [Category.assoc]
  erw [← he, ← P.map_comp, Iso.inv_hom_id_app, P.map_id, Iso.inv_hom_id_app]
  change 𝟙 _ = 𝟙 _
  rfl

private lemma identity_exchange_left
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S] (f : T ⟶ S)
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A f).map ((unboundedEtaleLowerShriekId A S).inv.app K) ≫
      (rightDerivedLowerShriekBaseChangeMap A (IsPullback.id_vert f)).app K =
    (unboundedEtaleLowerShriekId A T).inv.app ((ordinaryFinitePullback A f).obj K) := by
  let u := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f
  let R := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T)
  have h := identity_exchange A f K
  simp only [unboundedEtaleCompactSupportBaseChange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  apply (cancel_epi (u.inv.app K)).mp
  apply (cancel_mono (R.map (u.hom.app K))).mp
  simp only [Category.assoc]
  have hn := u.inv.naturality ((unboundedEtaleLowerShriekId A S).inv.app K)
  erw [← reassoc_of% hn]
  erw [h]
  have ht := (unboundedEtaleLowerShriekId A T).inv.naturality (u.hom.app K)
  simp only [Functor.id_map] at ht
  erw [← ht, Iso.inv_hom_id_app_assoc]

-- The mate calculation from WeilConjectures.TraceFormula.CurvePieces, at arbitrary categories.
private lemma mate_identity {C D : Type*} [Category C] [Category D]
    {L₁ R₁ : C ⥤ C} {L₂ R₂ : D ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ 𝟭 C) (e₂ : L₂ ≅ 𝟭 D)
    (G : C ⥤ D) (α : TwoSquare G L₁ L₂ G)
    (hα : ∀ X, α.natTrans.app X = e₂.hom.app (G.obj X) ≫ G.map (e₁.inv.app X))
    (X : C) :
    (mateEquiv adj₁ adj₂ α).natTrans.app X =
      G.map ((conjugateIsoEquiv adj₁ Adjunction.id e₁.symm).hom.app X) ≫
        (conjugateIsoEquiv adj₂ Adjunction.id e₂.symm).inv.app (G.obj X) := by
  have h := ((conjugateIsoEquiv adj₂ Adjunction.id e₂.symm).inv.naturality
    (G.map (e₁.inv.app (R₁.obj X) ≫ adj₁.counit.app X)))
  simp only [conjugateIsoEquiv, conjugateEquiv, mateEquiv_apply, Adjunction.id, Iso.symm_hom,
    Iso.symm_inv, Equiv.coe_fn_mk] at h ⊢
  simpa [hα] using h.symm

private lemma compact_comparison_eq (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineLinearCompactComparison N hN A hA S hS d =
      (affineTraceUnboundedCompactComparison A S d).app
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) := by
  let K : DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, Exists.elim (exists_affineSpaceTopTrace N hN A hA) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 S hS d).2.1))⟩
  apply Iso.ext
  change (affineTracePlusCompatibility A S d).inv.app K ≫
    DerivedCategory.Plus.ι.map ((affineTraceCompactSupportComparison A S d).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
        (affineTraceProjection S d)).hom.app K =
    (affineTraceUnboundedCompactComparison A S d).hom.app (DerivedCategory.Plus.ι.obj K)
  apply (cancel_epi ((affineTracePlusCompatibility A S d).hom.app K)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (affineTraceUnboundedCompactComparison_restriction A S d K).symm

private lemma compact_comparison_zero (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (affineLinearCompactComparison N hN A hA S hS 0).inv =
      (unboundedEtaleLowerShriekId A S).hom.app (ordinaryFiniteUnit A S) := by
  exact congrArg Iso.inv (compact_comparison_eq N hN A hA S hS 0)

private lemma adjoint_identity_calculation {C : Type*} [Category C]
    {L R : C ⥤ C} (adj : L ⊣ R) (e : L ≅ 𝟭 C) (K : C) :
    adj.homEquiv K K (e.hom.app K) =
      ((conjugateIsoEquiv adj Adjunction.id) e.symm).inv.app K := by
  simp only [conjugateIsoEquiv_apply_inv, Iso.symm_inv, conjugateEquiv,
    Adjunction.id, Adjunction.homEquiv_unit]
  simp

private lemma adjunct_zero (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    bundleSectionAffineAdjunct N hN A hA t D S hS 0 =
      ((conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (𝟙 S))
        Adjunction.id) (unboundedEtaleLowerShriekId A S).symm).inv.app
          (ordinaryFiniteUnit A S) := by
  have htrace : affineTraceCounit A N hA t D S hS 0 =
      𝟙 (ordinaryFiniteUnit A S) := by
    unfold affineTraceCounit affineTraceAdjunction
    rfl
  unfold bundleSectionAffineAdjunct
  rw [compact_comparison_zero, htrace]
  change (rightDerivedUpperShriekAdjunction A (𝟙 S)).homEquiv _ _
    ((unboundedEtaleLowerShriekId A S).hom.app (ordinaryFiniteUnit A S) ≫
      𝟙 (ordinaryFiniteUnit A S)) = _
  exact (congrArg ((rightDerivedUpperShriekAdjunction A (𝟙 S)).homEquiv
    (ordinaryFiniteUnit A S) (ordinaryFiniteUnit A S))
      (Category.comp_id ((unboundedEtaleLowerShriekId A S).hom.app
        (ordinaryFiniteUnit A S)))).trans
    (adjoint_identity_calculation (rightDerivedUpperShriekAdjunction A (𝟙 S))
      (unboundedEtaleLowerShriekId A S) (ordinaryFiniteUnit A S))

private lemma identity_exceptional_exchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S] (f : T ⟶ S)
    (K : DerivedCategoryModule A S) :
    (rightDerivedUpperShriekBaseChangeMap A (IsPullback.id_vert f)).app K =
      (ordinaryFinitePullback A f).map
        (((conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (𝟙 S))
          Adjunction.id) (unboundedEtaleLowerShriekId A S).symm).hom.app K) ≫
      ((conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (𝟙 T))
        Adjunction.id) (unboundedEtaleLowerShriekId A T).symm).inv.app
          ((ordinaryFinitePullback A f).obj K) := by
  have : IsIso (rightDerivedLowerShriekBaseChangeMap A (IsPullback.id_vert f)) :=
    isIso_rightDerivedLowerShriekBaseChangeMap A _
  apply mate_identity (rightDerivedUpperShriekAdjunction A (𝟙 S))
    (rightDerivedUpperShriekAdjunction A (𝟙 T))
    (unboundedEtaleLowerShriekId A S) (unboundedEtaleLowerShriekId A T)
    (ordinaryFinitePullback A f)
    (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap A
      (IsPullback.id_vert f)))) _ K
  intro X
  change (inv (rightDerivedLowerShriekBaseChangeMap A (IsPullback.id_vert f))).app X = _
  have h := identity_exchange_left A f X
  apply (cancel_mono ((rightDerivedLowerShriekBaseChangeMap A
    (IsPullback.id_vert f)).app X)).mp
  simp only [Category.assoc]
  rw [h, Iso.hom_inv_id_app]
  exact congr_app (IsIso.inv_hom_id
    (rightDerivedLowerShriekBaseChangeMap A (IsPullback.id_vert f))) X

private lemma section_square_eq (A : Type (u + 1)) [CommRing A]
    {X U S T : Scheme.{u}} (z : S ⟶ X) (w : T ⟶ U) (h : U ⟶ X) (v : T ⟶ S)
    (hw : w ≫ h = v ≫ z) (K : DerivedCategoryModule A X)
    (m : T ⟶ X) (hm : m = v ≫ z) :
    bundleSectionPullbackSquare A z w h v hw K =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v z m hm).symm.app K ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w h m
          (hm.trans hw.symm)).app K := by
  subst m
  rfl

private lemma identity_section_square (A : Type (u + 1)) [CommRing A]
    {T S : Scheme.{u}} (f : T ⟶ S) (K : DerivedCategoryModule A S) :
    (bundleSectionPullbackSquare A (𝟙 S) (𝟙 T) f f
      ((Category.id_comp f).trans (Category.comp_id f).symm) K).hom ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app
        ((ordinaryFinitePullback A f).obj K) =
      (ordinaryFinitePullback A f).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app K) := by
  rw [section_square_eq A (𝟙 S) (𝟙 T) f f _ K f (Category.comp_id f).symm]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
  erw [leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} A) f K,
    Category.comp_id]
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    f (𝟙 S) f (Category.comp_id f).symm).hom.app K)).mp
  rw [Iso.hom_inv_id_app]
  exact (leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) f K).symm

private lemma section_unit_calculation
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {I R : C ⥤ C} {J Q : D ⥤ D}
    (i : I ≅ 𝟭 C) (j : J ≅ 𝟭 D) (c : R ≅ 𝟭 C) (d : Q ≅ 𝟭 D)
    {K : C} {L : D} (u : P.obj K ⟶ L)
    (s : P.obj (I.obj (R.obj K)) ⟶ J.obj (P.obj (R.obj K)))
    (hs : s ≫ j.hom.app _ = P.map (i.hom.app _)) :
    s ≫ J.map (P.map (c.hom.app K) ≫ d.inv.app (P.obj K) ≫ Q.map u) ≫
        j.hom.app (Q.obj L) ≫ d.hom.app L =
      P.map (i.hom.app (R.obj K) ≫ c.hom.app K) ≫ u := by
  rw [← Category.assoc _ (j.hom.app _) (d.hom.app _)]
  rw [j.hom.naturality]
  simp only [Functor.id_map, Category.assoc]
  rw [reassoc_of% hs, d.hom.naturality u]
  simp only [Functor.id_map, Iso.inv_hom_id_app_assoc, Functor.map_comp, Category.assoc]

private lemma identity_section_comparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S] (f : T ⟶ S) :
    bundleSectionComparison A (𝟙 S) (𝟙 T) f f (IsPullback.id_vert f)
        (𝟙 S) (𝟙 T) ((Category.id_comp f).trans (Category.comp_id f).symm) ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app _ ≫
      ((conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (𝟙 T))
        Adjunction.id) (unboundedEtaleLowerShriekId A T).symm).hom.app _ =
    (ordinaryFinitePullback A f).map
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app _ ≫
        ((conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (𝟙 S))
          Adjunction.id) (unboundedEtaleLowerShriekId A S).symm).hom.app _) ≫
      (ordinaryFiniteUnitPullback A f).hom := by
  dsimp only [bundleSectionComparison]
  rw [identity_exceptional_exchange]
  simp only [Category.assoc]
  exact section_unit_calculation (ordinaryFinitePullback A f)
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S)
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T)
    (conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (𝟙 S))
      Adjunction.id (unboundedEtaleLowerShriekId A S).symm)
    (conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (𝟙 T))
      Adjunction.id (unboundedEtaleLowerShriekId A T).symm)
    (ordinaryFiniteUnitPullback A f).hom _
    (identity_section_square A f _)

private lemma pullback_id_eq (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    affineLinearPullbackId A S = leftDerivedUpperStarId (ModuleCat.{u + 1} A) S := by
  simp [affineLinearPullbackId, leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

/-- The inverse identity-adjunction comparison has the prescribed affine-frame restriction.
Source: orientation-charts proof Step 4, identity normalization in rank zero.
(blueprint: lem-trf-bundle-section-rank-zero-affine-normalization).

Proof: in rank zero affineTraceTower T 0 and affineTraceProjection T 0 are T and its
identity. The ordered adjunction is Adjunction.id, and its counit is the identity.
The inverse frame carries the zero section to the identity, because its composite with
that projection is the identity. Paste the frame square with the square identifying the
bundle projection with the identity via e. The compact-support exchange pasting and
identity laws identify their exceptional mates. Under the pullback identity unitor,
conjugating the identity compact-support comparison gives precisely
bundleSectionRankZeroComparison. The zero-stage coefficient descent is the pullback
identity comparison, and the zero-stage base coefficient comparison is the constant-unit
pullback comparison. Substituting these into the pasted mate equation gives the displayed
inverse-map normalization. This is an equation on one arbitrary affine frame, and asserts
neither the existence of e nor equality with an arbitrary normalized orientation. The
identity and pasting laws also apply over empty schemes and to zero coefficient rings.
-/
theorem bundleSectionRankZero_affineNormalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank 0]
    (e : VectorBundleZeroSection.scheme S 0 M ≅ S)
    (hp : e.hom = VectorBundleZeroSection.π S 0 M)
    (hz : e.inv = VectorBundleZeroSection.zero S 0 M)
    [IsIso (bundleSectionRankZeroComparison A S M e hz)]
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (V : S.Opens) (hV : IsAffine V.toScheme)
    (f : VectorBundleZeroSection.Trivialization S 0 M V) :
    (ordinaryFinitePullback A V.ι).map
        (inv (bundleSectionRankZeroComparison A S M e hz)) ≫
        bundleSectionChartComparison A S 0 M V f =
      (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS 0).hom ≫
        (bundleSectionChartCoefficient N A hA t S hS 0 M V f).inv ≫
        (ordinaryFinitePullback A (bundleSectionChartZero S 0 M V f)).map
          (bundleSectionAffineAdjunct N hN A hA t D V.toScheme
            (affineTracePullbackInvertible N V.ι hS) 0) := by
  have hchart : vectorIntegrationChart S 0 M V f =
      V.ι ≫ VectorBundleZeroSection.zero S 0 M := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, ← hz, e.inv_hom_id, Category.comp_id]
    simpa only [hp, affineTraceProjection, Category.id_comp] using
      (vectorIntegrationChart_isPullback S 0 M V f).w
  have hchart' : vectorIntegrationChart S 0 M V f = V.ι ≫ e.inv := by
    rw [hz]
    exact hchart
  have he : e.inv ≫ VectorBundleZeroSection.π S 0 M = 𝟙 S := by
    rw [← hp]
    exact e.inv_hom_id
  have hc := bundleSectionComparison_iso_pasting A
    (VectorBundleZeroSection.π S 0 M) (𝟙 S) (𝟙 V.toScheme) e.symm he
    V.ι V.ι (IsPullback.id_vert V.ι)
    (by simpa only [hchart', affineTraceProjection, Iso.symm_hom] using
      vectorIntegrationChart_isPullback S 0 M V f)
    (VectorBundleZeroSection.zero S 0 M) (𝟙 S) (𝟙 V.toScheme)
    (by simpa only [Category.id_comp, Iso.symm_hom] using hz)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    (by simp only [Category.id_comp, Iso.symm_hom, hz])
  have hi := identity_section_comparison A V.ι
  suffices ∀ (w : V.toScheme ⟶ V.toScheme)
      (hw : w ≫ vectorIntegrationChart S 0 M V f =
        V.ι ≫ VectorBundleZeroSection.zero S 0 M)
      (hw0 : w ≫ affineTraceProjection V.toScheme 0 = 𝟙 V.toScheme),
      (ordinaryFinitePullback A V.ι).map
          (inv (bundleSectionRankZeroComparison A S M e hz)) ≫
        bundleSectionComparison A (VectorBundleZeroSection.π S 0 M)
          (affineTraceProjection V.toScheme 0) (vectorIntegrationChart S 0 M V f) V.ι
          (vectorIntegrationChart_isPullback S 0 M V f)
          (VectorBundleZeroSection.zero S 0 M) w hw =
      (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS 0).hom ≫
        ((ordinaryFinitePullback A w).mapIso
            (affineLinearCoefficientDescent A N hA t V.toScheme
              (affineTracePullbackInvertible N V.ι hS) 0) ≪≫
          (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
            w (affineTraceProjection V.toScheme 0) hw0).app _).inv ≫
        (ordinaryFinitePullback A w).map
          (bundleSectionAffineAdjunct N hN A hA t D V.toScheme
            (affineTracePullbackInvertible N V.ι hS) 0) by
    exact this (bundleSectionChartZero S 0 M V f)
      ((vectorIntegrationChart_isPullback S 0 M V f).lift_fst _ _ _)
      ((vectorIntegrationChart_isPullback S 0 M V f).lift_snd _ _ _)
  intro w hw hw0
  have hwid : w = 𝟙 V.toScheme := by
    simpa only [affineTraceProjection, Category.comp_id] using hw0
  subst w
  have hn : bundleSectionComparison A (VectorBundleZeroSection.π S 0 M)
        (𝟙 V.toScheme) (vectorIntegrationChart S 0 M V f) V.ι
        (vectorIntegrationChart_isPullback S 0 M V f)
        (VectorBundleZeroSection.zero S 0 M) (𝟙 V.toScheme)
        (by simp only [Category.id_comp, hchart]) ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) V.toScheme).hom.app _ ≫
        ((conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (𝟙 V.toScheme))
          Adjunction.id) (unboundedEtaleLowerShriekId A V.toScheme).symm).hom.app _ =
      (ordinaryFinitePullback A V.ι).map
        (bundleSectionRankZeroComparison A S M e hz) ≫
        (ordinaryFiniteUnitPullback A V.ι).hom := by
    simp only [hchart', Iso.symm_hom] at hc ⊢
    rw [← hc]
    simp only [Category.assoc]
    rw [hi]
    simp only [bundleSectionRankZeroComparison, Functor.map_comp, Category.assoc, hz]
    rfl
  apply (cancel_mono
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) V.toScheme).hom.app
        ((rightDerivedUpperShriek A (𝟙 V.toScheme)).obj (ordinaryFiniteUnit A V.toScheme)) ≫
      ((conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (𝟙 V.toScheme))
        Adjunction.id) (unboundedEtaleLowerShriekId A V.toScheme).symm).hom.app
          (ordinaryFiniteUnit A V.toScheme))).mp
  simp only [Category.assoc]
  rw [hn, ← Functor.map_comp_assoc, IsIso.inv_hom_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [vectorIntegrationBaseCoefficientPullback, Nat.rec_zero,
    adjunct_zero, affineLinearCoefficientDescent, Iso.trans_inv, Functor.mapIso_inv,
    Iso.symm_inv, Iso.app_inv, pullback_id_eq]
  dsimp only [leftDerivedUpperStarCompSectionIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Iso.app_inv]
  simp only [Category.assoc]
  erw [reassoc_of% (leftDerivedUpperStarId (ModuleCat.{u + 1} A) V.toScheme).hom.naturality
    (((conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (𝟙 V.toScheme))
      Adjunction.id) (unboundedEtaleLowerShriekId A V.toScheme).symm).inv.app
        (ordinaryFiniteUnit A V.toScheme))]
  simp only [Iso.inv_hom_id_app]
  erw [leftDerivedUpperStarComp_id_right_hom_app_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  all_goals exact (Category.comp_id _).symm

end AlgebraicGeometry.Etale
