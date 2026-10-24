/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement

import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-!
# The pushforward along a closed immersion on pro-étale abelian sheaves

This is the version for abelian sheaves of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`, with the
same proof: for a closed immersion `i : Z ⟶ X` the counit `i^* i_* G ⟶ G` of the pro-étale
adjunction `i^* ⊣ i_*` on abelian sheaves is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit_addCommGrp`, blueprint
`lem-exc-proetale-closed-fully-faithful`), so `i_*` is fully faithful.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {Z U X : Scheme.{u}}

private lemma closedSitePrecompFullyFaithful (A : Type u) [CommRing A] (I : Ideal A) :
    Nonempty (((Functor.whiskeringLeft _ _ Ab.{u + 1}).obj
      (AffineProEt.closedSiteBaseChange A I).op).FullyFaithful) := by
  obtain ⟨adj, h⟩ := AffineProEt.exists_closedSiteAdjunction A I
  have : IsIso adj.unit := h
  let adjp := adj.op.whiskerLeft Ab.{u + 1}
  have : ∀ F, IsIso (adjp.counit.app F) := fun F => by
    have : ∀ X, IsIso ((adjp.counit.app F).app X) := fun X => by
      change IsIso (F.map (adj.unit.app X.unop).op)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have : IsIso adjp.counit := NatIso.isIso_of_isIso_app _
  exact ⟨adjp.fullyFaithfulROfIsIsoCounit⟩

private lemma isIso_closedCounit_of_quotient (A : Type u) [CommRing A] (I : Ideal A) :
    IsIso (upperStarLowerStarAdjunction Ab.{u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).counit := by
  obtain ⟨hpre⟩ := closedSitePrecompFullyFaithful A I
  let F := lowerStar Ab.{u + 1}
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  let RX := (AffineProEt.toProEt (Spec (.of A))).sheafPushforwardContinuous
    Ab.{u + 1} (AffineProEt.topology (Spec (.of A))) (ProEt.topology (Spec (.of A))) ⋙
    sheafToPresheaf (AffineProEt.topology (Spec (.of A))) Ab.{u + 1}
  let RZ := (AffineProEt.toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous
    Ab.{u + 1} (AffineProEt.topology (Spec (.of (A ⧸ I))))
      (ProEt.topology (Spec (.of (A ⧸ I)))) ⋙
    sheafToPresheaf (AffineProEt.topology (Spec (.of (A ⧸ I)))) Ab.{u + 1}
  have hRZ : RZ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  have hcomp : (F ⋙ RX).FullyFaithful := hRZ.comp hpre
  have hF : F.FullyFaithful := hcomp.ofCompFaithful
  have : F.Full := hF.full
  have : F.Faithful := hF.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

private lemma isIso_closedCounit_of_isAffine {Z X : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso (upperStarLowerStarAdjunction Ab.{u + 1} i).counit := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := i ≫ X.isoSpec.hom)).mp inferInstance
  have hq := isIso_closedCounit_of_quotient (Γ(X, ⊤)) I
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : (q)_*[Ab.{u + 1}].Full :=
    (upperStarLowerStarAdjunction Ab.{u + 1} q).fullyFaithfulROfIsIsoCounit.full
  have : (q)_*[Ab.{u + 1}].Faithful :=
    (upperStarLowerStarAdjunction Ab.{u + 1} q).fullyFaithfulROfIsIsoCounit.faithful
  have h : ((e.hom)_*[Ab.{u + 1}] ⋙ (q)_*[Ab.{u + 1}]).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  have h' := h.ofIso (lowerStarComp Ab.{u + 1} e.hom q ≪≫
    lowerStarCongr Ab.{u + 1} he.symm)
  have h'' : ((i)_*[Ab.{u + 1}] ⋙
      (X.isoSpec.hom)_*[Ab.{u + 1}]).FullyFaithful :=
    h'.ofIso (lowerStarComp Ab.{u + 1} i X.isoSpec.hom).symm
  have hF := h''.ofCompFaithful
  have := hF.full
  have := hF.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

private lemma isIso_map_counit_of_local_adjunction
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    (ai : L₁ ⊣ R₁) (ai' : L₂ ⊣ R₂) (aj : F₁ ⊣ U₁) (aj' : F₂ ⊣ U₂)
    (α : TwoSquare U₂ R₂ R₁ U₁) [IsIso α.natTrans]
    (hb : IsIso (((mateEquiv aj' aj).symm α).natTrans))
    (hc : IsIso ai'.counit) (M : B) : IsIso (F₂.map (ai.counit.app M)) := by
  let β := (mateEquiv aj' aj).symm α
  let γ := (mateEquiv ai ai').symm β
  have : IsIso β.natTrans := hb
  have : IsIso γ.natTrans := by
    dsimp [γ, β]
    rw [iterated_mateEquiv_conjugateEquiv_symm ai ai' aj aj']
    change IsIso ((conjugateEquiv (ai.comp aj') (aj.comp ai')).symm α.natTrans)
    infer_instance
  have h := mateEquiv_counit_symm ai ai' β M
  have : IsIso ai'.counit := hc
  have : IsIso (L₂.map (β.app M) ≫ ai'.counit.app (F₂.obj M)) := inferInstance
  rw [h] at this
  exact IsIso.of_isIso_comp_left (γ.natTrans.app _) _

private lemma isIso_closedCounit_localization {U' U Z' Z : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
    [WeaklyEtale j] [WeaklyEtale j'] (sq : IsPullback g' j' j g'')
    (hc : IsIso (upperStarLowerStarAdjunction Ab.{u + 1} g').counit)
    (F : Sheaf (ProEt.topology Z') Ab.{u + 1}) :
    IsIso ((localizationRestriction Ab.{u + 1} j' inferInstance).map
      ((upperStarLowerStarAdjunction Ab.{u + 1} g'').counit.app F)) := by
  let ai := upperStarLowerStarAdjunction Ab.{u + 1} g''
  let ai' := upperStarLowerStarAdjunction Ab.{u + 1} g'
  let aj := localizationRestrictionLowerStarAdjunction Ab.{u + 1} j inferInstance
  let aj' := localizationRestrictionLowerStarAdjunction Ab.{u + 1} j' inferInstance
  let α := TwoSquare.mk _ _ _ _ (squareLowerStarIso Ab.{u + 1} sq.toCommSq).hom
  let β := (mateEquiv aj' aj).symm α
  have hβ : β.natTrans = localizationRestrictionBaseChangeMap
      Ab.{u + 1} sq.toCommSq := by
    apply (mateEquiv aj' aj).injective
    change (mateEquiv aj' aj) ((mateEquiv aj' aj).symm α) = _
    rw [Equiv.apply_symm_apply]
    exact (mateEquiv_localizationRestrictionBaseChangeMap
      Ab.{u + 1} sq.toCommSq).symm
  have : IsIso β.natTrans := by
    rw [hβ]
    exact isIso_localizationRestrictionBaseChangeMap_of_isPullback _ sq
  exact isIso_map_counit_of_local_adjunction ai ai' aj aj' α this hc F


/-- Blueprint `lem-exc-proetale-closed-fully-faithful` (subsection
`sk-prop-sf-open-closed-triangle`): for a closed immersion `i : Z ⟶ X` the counit
`i^* i_* G ⟶ G` of the pro-étale adjunction `i^* ⊣ i_*` is an isomorphism on all pro-étale
sheaves of modules; so `i_*` is fully faithful, without a constructibility hypothesis.

Proof: on the affine pro-étale bases of Spec A and Spec (A/I), closed base change is
right adjoint to the closed-site lift with invertible unit. Opposites and precomposition
therefore make direct image fully faithful on presheaves. Restriction to these bases is
an equivalence on sheaves, so the same holds for sheaves of modules. An arbitrary closed
immersion into an affine scheme is isomorphic to such a quotient immersion. Finally,
restrict the counit to the inverse image of an affine open cover of the target. Weakly
étale base change and the double-mate identity identify these restrictions with the affine
counits, up to isomorphisms. Open-cover conservativity proves the global claim. -/
theorem isIso_upperStarLowerStarAdjunction_counit_addCommGrp (i : Z ⟶ X)
    [IsClosedImmersion i] :
    IsIso (upperStarLowerStarAdjunction Ab.{u + 1} i).counit := by
  have happ (F : Sheaf (ProEt.topology Z) Ab.{u + 1}) :
      IsIso ((upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app F) := by
    let U (k : X.affineCover.I₀) := pullback (X.affineCover.f k) i
    let j (k : X.affineCover.I₀) : U k ⟶ Z := pullback.snd _ _
    have : ∀ k, IsOpenImmersion (j k) := fun k => inferInstance
    have hsurj : ∀ z, ∃ k, z ∈ Set.range (j k).base := by
      intro z
      obtain ⟨x, hx⟩ := X.affineCover.covers (i.base z)
      obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback x z hx
      exact ⟨X.affineCover.idx (i.base z), w, hw⟩
    have hcover : Presieve.ofArrows U j ∈ Scheme.proetalePrecoverage Z :=
      Scheme.zariskiPrecoverage_le_proetalePrecoverage _
        ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hsurj, fun k => this k⟩)
    refine isIso_of_isIso_localizationRestriction Ab.{u + 1} _ j hcover
      fun k => ?_
    exact isIso_closedCounit_localization (IsPullback.of_hasPullback (X.affineCover.f k) i)
      (isIso_closedCounit_of_isAffine (pullback.fst (X.affineCover.f k) i)) F
  exact NatIso.isIso_of_isIso_app _

end ProEtale

end AlgebraicGeometry
