/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActualSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.AlgebraicGeometry.AdicUnliftedPerfectCharts
import all WeilConjectures.AlgebraicGeometry.OrdinaryIntegralLocalModels
import all WeilConjectures.AlgebraicGeometry.IntegralCompletedLocalPerfectCriterion
import all WeilConjectures.AlgebraicGeometry.PbcUniformReductionCriterion
import all WeilConjectures.AlgebraicGeometry.IntegralPullbackScalarComparison
import all WeilConjectures.AlgebraicGeometry.ExtensionZeroPerfectModelTransport
import all WeilConjectures.AlgebraicGeometry.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActualSupplement
import WeilConjectures.AlgebraicGeometry.CechPerfectModelCompleteness

/-! # Local perfect models over the actual valuation ring

Source: Bhatt--Scholze, Proposition 6.6.11 and Definition 6.5.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

namespace PadicLocalCriterion

/-- Completeness is detected on the given perfect charts, for any adic datum. -/
private theorem chart_complete (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (hK : IsIntegralStratifiedPerfect T d K) :
    PbcIsIntrinsicallyComplete T d K := by
  classical
  let : IsNoetherianRing A := d.noetherian
  obtain ⟨s, hs⟩ := hK
  choose W hW hw using hs
  let e (i : Fin s.n) : ProEt.mk (𝟙 (s.domain i)) ≅ ⊤_ (s.domain i).ProEt :=
    (terminalIdentity _).uniqueUpToIso terminalIsTerminal
  have covers (i : Fin s.n) : ∃ R : Presieve (ProEt.mk (𝟙 (s.domain i))),
      R ∈ ProEt.precoverage (s.domain i) _ ∧ R ≤ (W i).pullback (e i).hom := by
    have : (ProEt.precoverage (s.domain i)).IsStableUnderComposition := by
      dsimp [ProEt.precoverage]; infer_instance
    have : (ProEt.precoverage (s.domain i)).IsStableUnderBaseChange := by
      dsimp [ProEt.precoverage]; infer_instance
    have : (ProEt.precoverage (s.domain i)).HasIsos := by
      dsimp [ProEt.precoverage]; infer_instance
    exact (ProEt.precoverage (s.domain i)).mem_toGrothendieck_iff_of_isStableUnderComposition.mp
      ((ProEt.topology (s.domain i)).pullback_stable (e i).hom (hW i))
  choose R hR hRW using covers
  let H (i : Fin s.n) := (R i).preZeroHypercover
  let F (i : Fin s.n) := ProEt.forget (s.domain i) ⋙ Over.forget (s.domain i)
  let V (i : Fin s.n) : Scheme.Cover.{u + 1} proetalePrecoverage (s.domain i) :=
    { toPreZeroHypercover := (H i).map (F i)
      mem₀ := by
        rw [PreZeroHypercover.presieve₀_map, Presieve.presieve₀_preZeroHypercover]
        exact hR i }
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  apply (wfComplete_iff_presentation T d r a ha K).mp
  apply (stratum_completion_unit_restriction d T s.toFiniteLocallyClosed V r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)).mpr
  intro i j C eC
  change Fin s.n at i
  have := s.isImmersion i
  obtain ⟨P, hP, he⟩ := hw i ((H i).X j) ((H i).f j ≫ (e i).hom) (hRW i _ _ j.2)
  have hf : (V i).f j = ((H i).X j).hom := by
    have hh := MorphismProperty.Over.w ((H i).f j)
    change ((H i).f j).left ≫ 𝟙 (s.domain i) = ((H i).X j).hom at hh
    change ((H i).f j).left = ((H i).X j).hom
    exact (Category.comp_id ((H i).f j).left).symm.trans hh
  have hlocal (f : ((H i).X j).left ⟶ s.domain i)
      (eC : DerivedCategory.Q.obj C ≅ (d.pull (f ≫ s.immersion i)).obj K)
      (hf : f = ((H i).X j).hom) :
      IsDerivedCompleteIntrinsic ((H i).X j).left d r a ha
        ((d.pull (f ≫ s.immersion i)).obj K) C eC := by
    subst f
    obtain ⟨χ⟩ := (localModel_iff d (s.immersion i) ((H i).X j) K P).mp he
    have h := cechPerfectModel_intrinsicComplete ((H i).X j).left d P hP
      r a ha C (eC ≪≫ χ)
    change IsIso (intrinsicCompletionUnit _ d r a ha _ C eC)
    change IsIso ((χ.inv ≫ eC.inv) ≫
      DerivedCategory.Q.map (intrinsicCompletionComplexUnit _ d r a C)) at h
    rw [Category.assoc] at h
    exact (isIso_comp_left_iff χ.inv _).mp h
  exact hlocal ((V i).f j) eC hf

/-- Retain the adjacent normalization equations when recovering etale origins. -/
private theorem chart_reductions (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (hK : PbcUniformReductionProfile T d K) :
    PbcHasUniformConstructibleReductions T d K ∧ PbcHasCompatibleEtaleOrigins T d K := by
  classical
  let M := pbcReductionAdicTower T d K
  have hlevels := (uniformProfile_localEffectivity T d K hK).1
  have levels (n : ℕ) := levelOrigin_realization T d M n (hlevels n)
  choose V hV W e using levels
  let W' (n : ℕ) := (W n).some
  let e' (n : ℕ) := (e n).some
  let δ (n : ℕ) := (pbcFunctionReduction T d n).symm.app (V (n + 1)) ≪≫
    (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).mapIso
      (e' (n + 1)) ≪≫ M.normalization (n + 1) n (Nat.le_succ n) ≪≫ (e' n).symm
  let θ (n : ℕ) := (pbcDerivedFunctionRealization T d n).preimageIso (δ n)
  obtain ⟨β, hβ⟩ := compatibleEtaleNormalizations T d V hV W' θ
  let P : AlgebraicGeometry.ProEtale.PbcWitnessedTower T d :=
    { K := V, boundedBelow := hV, origin := W', theta := θ,
      beta := β, compatibility := hβ }
  refine ⟨uniformProfile_uniformReductions T d K hK, P, e', fun n ↦ ?_⟩
  change (pbcDerivedFunctionRealization T d n).map (θ n).hom ≫ (e' n).hom = _
  change (pbcDerivedFunctionRealization T d n).map
    ((pbcDerivedFunctionRealization T d n).preimage (δ n).hom) ≫ (e' n).hom = _
  rw [Functor.map_preimage]
  dsimp only [δ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Reflect a raw inverse-image model through the exact scalar equivalence. -/
private theorem raw_model {T U : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (g : U ⟶ T) (K : PbcCompletedDerived T d)
    (P : completedConstantDerived (ModuleCat.{u + 1} A))
    (h : Nonempty ((adicTowerPullback g (pbcAdicCompletion T d)).obj K ≅
      (adicTowerPullback g (pbcAdicCompletion T d)).obj
        ((integralConstantDerived T d).obj P))) :
    Nonempty ((d.pull g).obj K ≅ (integralConstantDerived U d).obj P) := by
  let c := (adicLisseForget U).mapIso (d.integralRingIso g)
  let e := proEtaleScalarEquivalence U c
  have : e.functor.Additive := inferInstanceAs
    (SheafOfModules.restrictScalars c.hom).Additive
  let F := e.mapDerivedCategory.functor
  let t := derivedPullbackScalarIso g (pbcAdicCompletion T d)
    (pbcAdicCompletion U d) (d.integralRingIso g)
  obtain ⟨h⟩ := h
  exact ⟨F.preimageIso (t.app K ≪≫ h ≪≫
    (t.app ((integralConstantDerived T d).obj P)).symm) ≪≫
      (integralConstantDerivedPullIso d g).app P⟩

/-- Close the unlifted perfect charts under further restriction to get a sieve. -/
private theorem padic_stratified
    (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (hl : IsUnit (l : Γ(T, ⊤)))
    (K : PbcCompletedDerived T (pbcPadicCoefficientDatum l E))
    (hK : PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) K) :
    IsIntegralStratifiedPerfect T (pbcPadicCoefficientDatum l E) K := by
  classical
  let d := pbcPadicCoefficientDatum l E
  have hInv (t : T) : IsUnit (l : T.presheaf.stalk t) := by
    simpa only [map_natCast] using
      RingHom.isUnit_map (T.presheaf.germ ⊤ t trivial).hom hl
  obtain ⟨s, V, hm⟩ := pbc_adic_unlifted_perfect_charts T hdim l E hInv ⟨K, hK⟩
  refine ⟨s, fun i ↦ ?_⟩
  let (j : (V i).I₀) : WeaklyEtale ((V i).f j) :=
    proetalePrecoverage_le_precoverage_weaklyEtale _ (V i).mem₀ (.mk j)
  let U (j : (V i).I₀) : (s.domain i).ProEt := ProEt.mk ((V i).f j)
  let e : ProEt.mk (𝟙 (s.domain i)) ≅ ⊤_ (s.domain i).ProEt :=
    (terminalIdentity _).uniqueUpToIso terminalIsTerminal
  let f (j : (V i).I₀) : U j ⟶ ProEt.mk (𝟙 (s.domain i)) :=
    MorphismProperty.Over.homMk ((V i).f j) (Category.comp_id _) (by trivial)
  have hc : Sieve.ofArrows U f ∈ ProEt.topology (s.domain i) _ := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact (V i).mem₀
  refine ⟨Sieve.ofArrows U (fun j ↦ f j ≫ e.hom), ?_, ?_⟩
  · have hp := (ProEt.topology _).pullback_stable e.symm.hom hc
    rw [Sieve.pullback_ofArrows_of_iso U f e.symm] at hp
    simpa only [Iso.symm_inv] using hp
  · intro W z hz
    obtain ⟨j, v, _⟩ := Sieve.ofArrows.exists hz
    obtain ⟨P, hP, he⟩ := hm i j
    obtain ⟨he⟩ := raw_model d ((V i).f j ≫ s.immersion i) K P he
    refine ⟨P, hP, (localModel_iff d (s.immersion i) W K P).mpr ?_⟩
    have hw : W.hom ≫ s.immersion i = v.left ≫ ((V i).f j ≫ s.immersion i) := by
      have hv := MorphismProperty.Over.w v
      change v.left ≫ (V i).f j = W.hom at hv
      rw [← hv, Category.assoc]
    exact ⟨eqToIso (congrArg (fun g ↦ (d.pull g).obj K) hw) ≪≫
      (d.pullComp v.left ((V i).f j ≫ s.immersion i)).app K ≪≫
      (d.pull v.left).mapIso he ≪≫ (integralConstantDerivedPullIso d v.left).app P⟩

end PadicLocalCriterion

/-- The local-perfect criterion with the actual valuation ring, using the small
pro-etale site of each covering scheme rather than its equivalent slice site.
Source: Bhatt--Scholze, Proposition 6.6.11 and Definition 6.5.1
(blueprint: lem-weil-pbc-integral-padic-local-perfect-criterion).

Proof: membership gives a uniform constructible reduction tower and intrinsic
completeness. Refine the finitely many constructibility stratifications of the
bounded residue complex. On a pro-etale cover of each stratum this residue complex
is constant and perfect, since the residue ring is a field. The valuation ring is
complete for its uniformizer ideal. Residue-lisse perfect lifting therefore lifts
the residue complex to a bounded finite-projective complex over the valuation ring.
Completeness identifies its completed realization with the original local object.
The pro-etale slice over a covering object is equivalent to the pro-etale site of
its underlying scheme; transport the realization and its isomorphism through this
equivalence and the canonical completed-coefficient inverse-image comparison.

Conversely, finite-projective terms are retracts of finite sums of the completed
ring, hence complete, with finite locally constant reductions. Completeness is
local for pro-etale covers and is detected on the finite strata. Each stratum is
quasi-compact: choose finitely many covering members to get a single bound for all
reductions. Normalized constructible local effectivity supplies the uniform tower
with its common local models. Finite-level site comparison supplies etale origins;
bounded-below full faithfulness uniquely lifts the transition isomorphisms and
inverses, and faithfulness gives their cocycles. These are precisely the three
membership conditions. The empty stratification and zero complexes cause no
exception. All coefficient comparisons preserve the actual quotient projections. -/
theorem integralPadicLocalPerfectCriterion
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] [IsNoetherian T]
    (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n) (hl : IsUnit (l : Γ(T, ⊤)))
    (K : PbcCompletedDerived T (pbcPadicCoefficientDatum l E)) :
    PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) K ↔
      ∃ s : FiniteLocallyClosedStratification T, ∀ k : Fin s.n,
        ∃ V : Sieve (⊤_ (s.domain k).ProEt),
          V ∈ ProEt.topology (s.domain k) (⊤_ (s.domain k).ProEt) ∧
          ∀ (U : (s.domain k).ProEt) (f : U ⟶ ⊤_ (s.domain k).ProEt), V f →
            ∃ (P : CochainComplex
                (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
              (a b : ℤ),
              P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
              (∀ q : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E) (P.X q) ∧
                Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X q)) ∧
              Nonempty ((pbcActualDerivedPull (U.hom ≫ s.immersion k)
                (pbcPadicCoefficientDatum l E)).obj K ≅
                (integralConstantDerived U.left (pbcPadicCoefficientDatum l E)).obj
                  ((completedConstantQ _).obj P)) := by
  classical
  constructor
  · intro hK
    obtain ⟨s, hs⟩ := PadicLocalCriterion.padic_stratified T hdim l E hl K hK
    refine ⟨s.toFiniteLocallyClosed, fun i ↦ ?_⟩
    obtain ⟨V, hV, hm⟩ := hs i
    refine ⟨V, hV, fun U f hf ↦ ?_⟩
    obtain ⟨P, hP, he⟩ := hm U f hf
    obtain ⟨he⟩ := (localModel_iff (pbcPadicCoefficientDatum l E)
      (s.immersion i) U K P).mp he
    obtain ⟨C, a, b, ha, hb, hC, ⟨e⟩⟩ := hP
    exact ⟨C, a, b, ha, hb, hC,
      ⟨(pullbackDatumOrdinaryTransport (U.hom ≫ s.immersion i) _).app K ≪≫ he ≪≫
        (integralConstantDerived U.left _).mapIso e⟩⟩
  · rintro ⟨s, hs⟩
    let d := pbcPadicCoefficientDatum l E
    let t := Stratification.ofNoetherianSpace s.n s.stratum s.isLocallyClosed_stratum
      s.iUnion_stratum_eq_univ s.pairwise_disjoint_stratum s.domain s.immersion
      s.isImmersion s.range_immersion
    have hp : IsIntegralStratifiedPerfect T d K := by
      refine ⟨t, fun i ↦ ?_⟩
      obtain ⟨V, hV, hm⟩ := hs i
      refine ⟨V, hV, fun U f hf ↦ ?_⟩
      obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hm U f hf
      refine ⟨(completedConstantQ _).obj P, ⟨P, a, b, ha, hb, hP, ⟨Iso.refl _⟩⟩,
        (localModel_iff d (s.immersion i) U K _).mpr ?_⟩
      exact ⟨((pullbackDatumOrdinaryTransport (U.hom ≫ s.immersion i) d).app K).symm
        ≪≫ e⟩
    exact ⟨PadicLocalCriterion.chart_complete T d K hp,
      PadicLocalCriterion.chart_reductions T d K (perfect_uniformProfile T d K hp)⟩

end AlgebraicGeometry.Scheme
