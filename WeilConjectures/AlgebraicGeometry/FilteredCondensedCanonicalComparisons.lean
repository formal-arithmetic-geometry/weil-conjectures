/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FilteredCondensedRepresentingPairData
import WeilConjectures.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! # A step of filtered condensed representing-pair descent -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.FilteredCondensedRepresentingPair
private theorem lift_comp_compatibility
    {A B D : Type*} [Category A] [Category B] [Category D]
    (P : ObjectProperty A) (Q : ObjectProperty B) (R : ObjectProperty D)
    (J : A ⥤ B) (G : B ⥤ D)
    (hJ : ∀ K, Q ((P.ι ⋙ J).obj K)) (hG : ∀ K, R ((Q.ι ⋙ G).obj K)) :
    (Functor.associator (Q.lift (P.ι ⋙ J) hJ) (R.lift (Q.ι ⋙ G) hG) R.ι ≪≫
      Functor.isoWhiskerLeft _ (R.liftCompιIso (Q.ι ⋙ G) hG) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Q.liftCompιIso (P.ι ⋙ J) hJ) G ≪≫
      Functor.associator _ _ _) = Iso.refl _ := by
  ext K
  simp [ObjectProperty.liftCompιIso]

private theorem normalized_comparison
    {A B D Z : Type*} [Category A] [Category B] [Category D] [Category Z]
    (F : A ⥤ D) (G : B ⥤ Z) (T : D ⥤ Z)
    (e : F ≅ F) (d : G ≅ G) (he : e = Iso.refl _) (hd : d = Iso.refl _)
    (a : A) (b : B) (p : T.obj (F.obj a) ⟶ G.obj b) :
    T.map (e.inv.app a) ≫ p ≫ d.hom.app b = p := by
  subst e d
  simp

variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

open CompactSupportCondensedRealization
open CondensedRing

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
private theorem finite_projection_iso
    {E H : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ H) :
    IsIso (condensedProjection (Profinite.padicSubfieldRingObjMap l h) c) := by
  have : IsIso (condensedPushScalar (Profinite.padicSubfieldRingObjMap l h) c.g) :=
    inferInstanceAs (IsIso
      (CondensedRing.derivedPushHom (Profinite.padicSubfieldRingObjMap l h) c.g))
  unfold condensedProjection pasteScalar
  infer_instance

private theorem omega_projection_iso (E : PadicAlgCl.FiniteIntermediateField l)
    (C : PadicSubfieldConstructible X.left l E) :
    IsIso ((condensedProjection (Profinite.padicSubfieldRingObjToPadicAlgCl l E) c).app
      C.obj) := by
  have : LocallyOfFiniteType (c.overObj (f := f)).hom := by
    change LocallyOfFiniteType (c.g ≫ Y.hom)
    infer_instance
  have : QuasiCompact (c.overObj (f := f)).hom := by
    change QuasiCompact (c.g ≫ Y.hom)
    infer_instance
  have : IsSeparated (c.overObj (f := f)).hom := by
    change IsSeparated (c.g ≫ Y.hom)
    infer_instance
  have : IsOpenImmersion (c.overI (f := f)).left := by
    change IsOpenImmersion c.i
    infer_instance
  have hC := CondensedRing.boundedConstructible_openImmersionLowerShriek_obj
    (Profinite.continuousMapRingObj E) l (c.overI (f := f)) C
  obtain ⟨N, hN⟩ := hC.1.1
  have : ((CondensedRing.openImmersionLowerShriek
      (Profinite.continuousMapRingObj E) c.i).mapDerivedCategory.obj C.obj).IsGE N := hN
  have : IsIso ((condensedPushScalar
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E) c.g).app
      ((CondensedRing.openImmersionLowerShriek
        (Profinite.continuousMapRingObj E) c.i).mapDerivedCategory.obj C.obj)) :=
    CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE
      l c.g E _ N
  unfold condensedProjection pasteScalar
  dsimp only [NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.id_comp, Category.comp_id]
  infer_instance

set_option maxHeartbeats 800000 in
-- Matching the concrete scalar and support functors traverses large derived-category terms.
/-- The original projection mates restrict to the bounded constructible scalar comparisons.
Source: blueprint/latest, sec-smooth-purity/sk-thm-sp-qbar, coefficient compatibility;
lem-pur-compact-support-condensed-realization, finite and closure projections.
(blueprint: lem-pur-filtered-condensed-canonical-comparisons).

Proof: for each finite inclusion and each inclusion into the closure, take the original
proper/open projection mate. When the coefficient and scheme universes differ, first
lift the finite coefficient field to the scheme universe and transport the coefficient
categories and projection mate along the resulting ring equivalence. Apply
finiteProjection_isIso and omegaProjection_isIso there, then transport invertibility
back. Thus the original components on bounded constructible objects are invertible.
Conjugate through the
recorded inclusion compatibility isomorphisms, then lift the resulting transformation
through the fully faithful constructible inclusion. Naturality follows from that of
the projection. Lift its inverse in the same way. Faithfulness proves the inverse
identities and the displayed normalization equations. This uses the finite-valued
closure ring throughout, including for an empty source scheme. -/
theorem canonical_scalar_comparisons :
    ∃ s : ScalarComparisons l k c, s.IsCanonical l k c := by
  -- Specialize the existing subfield push comparisons directly, avoiding universe transport.
  let s : ScalarComparisons l k c :=
    { finite := fun {E H} h ↦ by
        have := finite_projection_iso l k c h
        exact NatIso.ofComponents
          (fun C ↦ ObjectProperty.isoMk _
            (asIso ((condensedProjection (Profinite.padicSubfieldRingObjMap l h) c).app
              C.obj)))
          (by
            intro C D a
            ext
            exact (condensedProjection (Profinite.padicSubfieldRingObjMap l h) c).naturality
              a.hom)
      omega := fun E ↦ by
        exact NatIso.ofComponents
          (fun C ↦ by
            have := omega_projection_iso l k c E C
            exact ObjectProperty.isoMk _
              (asIso ((condensedProjection
                (Profinite.padicSubfieldRingObjToPadicAlgCl l E) c).app C.obj)))
          (by
            intro C D a
            ext
            exact (condensedProjection
              (Profinite.padicSubfieldRingObjToPadicAlgCl l E) c).naturality a.hom) }
  refine ⟨s, ?_, ?_⟩
  · intro E H h C
    change (derivedExtendScalarsSubfield Y.left l h).map
        ((finiteCompatibility l k c E).inv.app C) ≫
      (condensedProjection (Profinite.padicSubfieldRingObjMap l h) c).app C.obj ≫
        (finiteCompatibility l k c H).hom.app
          ((constructibleExtendScalars X.left l h).obj C) = _
    have hE : finiteCompatibility l k c E = Iso.refl _ := by
      unfold finiteCompatibility
        ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationCompatibility
        ContinuousMapRingObj.boundedConstructibleLowerStarCompatibility
        CondensedRing.boundedConstructibleOpenImmersionLowerShriekCompatibility
      exact lift_comp_compatibility _ _ _ _ _ _ _
    have hH : finiteCompatibility l k c H = Iso.refl _ := by
      unfold finiteCompatibility
        ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationCompatibility
        ContinuousMapRingObj.boundedConstructibleLowerStarCompatibility
        CondensedRing.boundedConstructibleOpenImmersionLowerShriekCompatibility
      exact lift_comp_compatibility _ _ _ _ _ _ _
    exact normalized_comparison _ _ _ _ _ hE hH C
      ((constructibleExtendScalars X.left l h).obj C)
      ((condensedProjection (Profinite.padicSubfieldRingObjMap l h) c).app C.obj)
  · intro E C
    change (derivedExtendScalarsToPadicAlgCl Y.left l E).map
        ((finiteCompatibility l k c E).inv.app C) ≫
      (condensedProjection (Profinite.padicSubfieldRingObjToPadicAlgCl l E) c).app C.obj ≫
        (omegaCompatibility l k c).hom.app
          ((constructibleToPadicAlgCl X.left l E).obj C) = _
    have hE : finiteCompatibility l k c E = Iso.refl _ := by
      unfold finiteCompatibility
        ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationCompatibility
        ContinuousMapRingObj.boundedConstructibleLowerStarCompatibility
        CondensedRing.boundedConstructibleOpenImmersionLowerShriekCompatibility
      exact lift_comp_compatibility _ _ _ _ _ _ _
    have hOmega : omegaCompatibility l k c = Iso.refl _ := by
      unfold omegaCompatibility
        CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
        CondensedRing.boundedConstructibleLowerStarCompatibility
        CondensedRing.boundedConstructibleOpenImmersionLowerShriekCompatibility
      exact lift_comp_compatibility _ _ _ _ _ _ _
    exact normalized_comparison _ _ _ _ _ hE hOmega C
      ((constructibleToPadicAlgCl X.left l E).obj C)
      ((condensedProjection (Profinite.padicSubfieldRingObjToPadicAlgCl l E) c).app C.obj)

end WeilConjectures.FilteredCondensedRepresentingPair
