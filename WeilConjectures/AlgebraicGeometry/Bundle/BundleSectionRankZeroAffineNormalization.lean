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
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

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

private lemma pullback_id_eq (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    affineLinearPullbackId A S = leftDerivedUpperStarId (ModuleCat.{u + 1} A) S := by
  simp [affineLinearPullbackId, leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

end AlgebraicGeometry.Etale
