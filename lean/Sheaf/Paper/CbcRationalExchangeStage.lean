/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.NormalizedCoefficientFamilies
import all Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import all Sheaf.Paper.FiniteExtensionCompactSupportBaseChange
import Sheaf.Paper.WeilTensorProduct

/-! # Exchange at one rational coefficient stage

Source: current blueprint, coefficient coherence of units, counits and mates.
(blueprint: lem-cbc-rational-exchange-stage)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

variable {X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [IsNoetherian X'] [IsNoetherian Y']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]

private theorem localization_full
    (R : Type*) [CommRing R] (C : Type*) [Category C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [(shiftFunctor C (1 : ℤ)).Linear R] (p : R)
    (D : Type*) [Category D] :
    ((Functor.whiskeringLeft C (ScalarLocalization R C p) D).obj
      (ScalarLocalization.localization R C p)).Full := by
  classical
  have : ∀ n : ℤ, (shiftFunctor C n).Linear R :=
    ScalarLocalization.all_shift_linear R C
  let M := Submonoid.powers p
  let E := ScalarLocalization.rationalComparison R C p
  have : E.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : E.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : E.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : E.IsEquivalence := {}
  let Q := ScalarLocalization.localization R C p
  have fac : Q ⋙ E ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, E, ScalarLocalization.localization, ScalarLocalization.rationalComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  have : Q.IsLocalization (Rationalization.W M C) :=
    Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
      (Rationalization.W M C) Q E.asEquivalence.symm
      (Functor.isoWhiskerRight fac.symm E.inv ≪≫ (Functor.associator _ _ _) ≪≫
        Functor.isoWhiskerLeft Q E.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)
  exact Localization.full_whiskeringLeft Q (Rationalization.W M C) D

/-- The normalized exchange exists uniquely at a fixed raw rational stage.
No compatibility between different coefficient stages is asserted here.

Source: current blueprint, coefficient coherence and
thm-cbc-finite-extension; parent coefficient-coherence proof, step 16.
(blueprint: lem-cbc-rational-exchange-stage).

Proof: the preserves fields of H, H', P and P' put the two integral
composites in the same full constructible complete category. Fix a finite
set of generators of the ideal. The completed compact-support exchange is
natural on that full category: its proper factor is the strict-tower mate
and its open factor is the completion-unit-normalized open comparison.
Its value is independent of generators, since both open comparisons are
the unique maps whose precomposition with the completion unit is the same
ordinary open exchange. The proper factor does not depend on generators.
The tensor-Hom comparison identifies the canonical scalar localization
with Rationalization. Its universal property makes precomposition with
localization full, so it extends the integral natural transformation after
localizing its target. Use the four localization equations to identify the
resulting endpoints with H_E followed by P_E and P'_E followed by H'_E.
These equations give exactly the displayed HEq, including
any generating tuple. Conversely every raw rational object is the image of
an integral object, which is complete for any generating tuple. Thus this
component formula fixes every component, and natural-transformation
extensionality proves uniqueness. -/
theorem cbcRationalExchangeStage_existsUnique
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (H : CbcCompactSupportCoefficientFamily l Ω c)
    (H' : CbcCompactSupportCoefficientFamily l Ω c')
    (P : CbcCompletedPullCoefficientFamily l Ω g)
    (P' : CbcCompletedPullCoefficientFamily l Ω g')
    (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! τ : (H.family.base.Φ E ⋙ P.family.base.Φ E) ⟶
        (P'.family.base.Φ E ⋙ H'.family.base.Φ E),
      ∀ (K : pbcIntegralStage l Ω X E)
    (r : ℕ) (a : Fin r → PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (ha : Ideal.span (Set.range a) = (pbcStageDatum.{u} l Ω E).ideal)
    (hc : cbcCompleteProperty (pbcStageDatum.{u} l Ω E) X r a ha K.obj),
    ∃ (hs : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion ⋙
          (pbcStageDatum.{u} l Ω E).push c.g ⋙
            (pbcStageDatum.{u} l Ω E).completedPull g).obj K.obj))
      (ht : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        (((pbcStageDatum.{u} l Ω E).completedPull g' ⋙
          cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c'.i c'.isOpenImmersion ⋙
            (pbcStageDatum.{u} l Ω E).push c'.g).obj K.obj)),
      HEq (τ.app ((pbcStageLocalization l Ω X E).obj K))
        ((pbcStageLocalization l Ω Y' E).map
          (ObjectProperty.homMk (X := ⟨_, hs⟩) (Y := ⟨_, ht⟩)
            (completedCompactSupportExchange (pbcStageDatum.{u} l Ω E)
              c c' gbar properSquare openSquare r a ha ⟨K.obj, hc⟩))) := by
  classical
  let d := pbcStageDatum.{u} l Ω E
  let QX := pbcStageLocalization l Ω X E
  let QY := pbcStageLocalization l Ω Y' E
  let IH := pbcConditionalIntegral d
    (cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ d.push c.g) (H.preserves E)
  let IH' := pbcConditionalIntegral d
    (cbcDerivedOpenShriek d c'.i c'.isOpenImmersion ⋙ d.push c'.g) (H'.preserves E)
  let IP := pbcConditionalIntegral d (d.completedPull g) (P.preserves E)
  let IP' := pbcConditionalIntegral d (d.completedPull g') (P'.preserves E)
  let F := H.family.base.Φ E ⋙ P.family.base.Φ E
  let G := P'.family.base.Φ E ⋙ H'.family.base.Φ E
  have eF : QX ⋙ F = (IH ⋙ IP) ⋙ QY := by
    dsimp only [F, QX, QY, IH, IP, d]
    rw [← Functor.assoc, H.localization, Functor.assoc, P.localization, ← Functor.assoc]
  have eG : QX ⋙ G = (IP' ⋙ IH') ⋙ QY := by
    dsimp only [G, QX, QY, IH', IP', d]
    rw [← Functor.assoc, P'.localization, Functor.assoc, H'.localization, ← Functor.assoc]
  obtain ⟨r₀, a₀, ha₀⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let t : IH ⋙ IP ⟶ IP' ⋙ IH' :=
    { app := fun K ↦ ObjectProperty.homMk
        (completedCompactSupportExchange d c c' gbar properSquare openSquare r₀ a₀ ha₀
          ⟨K.obj, wfConstructible_complete X d r₀ a₀ ha₀ K⟩)
      naturality := by
        intro K L k
        apply ObjectProperty.hom_ext
        exact (completeCompactSupportProetale_isIso d c c' gbar properSquare openSquare
          r₀ a₀ ha₀ ⟨K.obj, wfConstructible_complete X d r₀ a₀ ha₀ K⟩
          K.property.2.2).2 ⟨L.obj, wfConstructible_complete X d r₀ a₀ ha₀ L⟩ k.hom }
  let W := (Functor.whiskeringLeft (pbcIntegralStage l Ω X E)
    (pbcStageCategory l Ω X E) (pbcStageCategory l Ω Y' E)).obj QX
  have : W.Full := localization_full (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (pbcIntegralStage l Ω X E) (pbcStageUniformizer.{u} l Ω E)
    (pbcStageCategory l Ω Y' E)
  let tq : QX ⋙ F ⟶ QX ⋙ G :=
    eqToHom eF ≫ Functor.whiskerRight t QY ≫ eqToHom eG.symm
  let τ : F ⟶ G := W.preimage tq
  have hτ : Functor.whiskerLeft QX τ = tq := W.map_preimage tq
  have ht (K : pbcIntegralStage l Ω X E)
      (r : ℕ) (a : Fin r → PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
      (ha : Ideal.span (Set.range a) = d.ideal)
      (hc : cbcCompleteProperty d X r a ha K.obj) :
      HEq (τ.app (QX.obj K))
        (QY.map (ObjectProperty.homMk
          (X := (IH ⋙ IP).obj K) (Y := (IP' ⋙ IH').obj K)
          (completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha
            ⟨K.obj, hc⟩))) := by
    have he := congr_app hτ K
    have hgen := finiteExtension_exchange_generators d c c' gbar properSquare openSquare
      r₀ a₀ ha₀ r a ha K.obj (wfConstructible_complete X d r₀ a₀ ha₀ K) hc
    have he' : t.app K = ObjectProperty.homMk
        (X := (IH ⋙ IP).obj K) (Y := (IP' ⋙ IH').obj K)
        (completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha
          ⟨K.obj, hc⟩) := by
      apply ObjectProperty.hom_ext
      exact hgen
    have hh : HEq (τ.app (QX.obj K)) (QY.map (t.app K)) := by
      change τ.app (QX.obj K) =
        (eqToHom eF).app K ≫ QY.map (t.app K) ≫ (eqToHom eG.symm).app K at he
      simp only [eqToHom_app] at he
      exact (conj_eqToHom_iff_heq _ _
        (congrArg (fun J ↦ J.obj K) eF)
        (congrArg (fun J ↦ J.obj K) eG)).mp he
    rw [he'] at hh
    exact hh
  refine ⟨τ, ?_, ?_⟩
  · intro K r a ha hc
    exact ⟨P.preserves E (IH.obj K), H'.preserves E (IP'.obj K), ht K r a ha hc⟩
  · intro σ hσ
    apply NatTrans.ext
    funext K
    rcases K with ⟨K⟩
    obtain ⟨hs, ht', he⟩ := hσ K r₀ a₀ ha₀ (wfConstructible_complete X d r₀ a₀ ha₀ K)
    exact eq_of_heq (he.trans (ht K r₀ a₀ ha₀
      (wfConstructible_complete X d r₀ a₀ ha₀ K)).symm)

end AlgebraicGeometry.Scheme
