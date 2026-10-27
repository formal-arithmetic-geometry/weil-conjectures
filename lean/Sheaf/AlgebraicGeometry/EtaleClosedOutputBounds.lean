/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ConstructibleExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
import Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude
import all Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude
import all Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.ComparisonTorInterval

/-! # Bounds on comparison pullbacks of etale closed-support values

Source: main-20261015, sec-smooth-purity/sk-prop-sp-et-proet/
thm-pur-general-admissibility.proof.md, Step 2; the closed-support computations
lem-exc-closed-amplitude and prop-exc-closed-tor; Stacks Tag 09AL
(blueprint: lem-pur-etale-closed-output-bounds).

The two implications have independent hypotheses. Ordinary etale closed support is
followed by the canonical exact comparison into intrinsic constant-ring modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem ulift_span_isMaximal (B : Type u) [CommRing B] (x : B)
    (hx : (Ideal.span {x}).IsMaximal) :
    (Ideal.span {(ULift.up x : ULift.{u + 1} B)}).IsMaximal := by
  have h := hx.map_bijective
    (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{u + 1} B)
    ULift.ringEquiv.symm.bijective
  have he : (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{u + 1} B) x =
      ULift.up x := rfl
  simpa only [Ideal.map_span, Set.image_singleton, he] using h

/-- Independent cohomological and Tor bounds for the ordinary etale closed right adjoint
and its comparison pullback. The intrinsic Tor predicate tests every degree-zero
pro-etale module sheaf, without any etale-origin restriction on the test object.
Source: main-20261015, thm-pur-general-admissibility.proof.md, Step 2,
lem-exc-closed-amplitude.proof.md and prop-exc-closed-tor.proof.md; Stacks Tag 09AL
(blueprint: lem-pur-etale-closed-output-bounds).

Proof:
1. For (a), apply lem-exc-closed-amplitude with input interval [r,s]. The two clauses
of def-exc-open-complement-bound supply its vanishing and constructibility hypotheses.
It gives etale constructibility and cohomology in [r,s+c+1], without a Tor assumption.
2. Apply lem-sf-proetale-constructible-origin (ii) on Z to that etale output. This gives
intrinsic bounded constructibility. The exactness and cohomology comparison of
lem-sf-comparison-pullback-exact identify each pulled-back cohomology sheaf with the
pullback of the corresponding etale cohomology sheaf. Thus vanishing outside the same
interval is preserved, giving def-weil-constructible-intervals on the pro-etale site.
3. For (b), start independently with the Tor interval of K and its bounded
constructibility. Apply prop-exc-closed-tor for the specified positive coefficient level,
closed immersion and quasi-compact complementary open. Its hypotheses are exactly the
two open-complement conditions. The etale output is bounded constructible and has Tor
amplitude [r,s+c+1]; the cohomological premise of (a) is not used.
4. This output is bounded below. Apply lem-exc-comparison-tor-interval in the forward
direction for [r,s+c+1]. A bounded flat model pulls back termwise, and its tensor with
any degree-zero pro-etale module sheaf has no terms, hence no cohomology, outside that
interval. Canonical constant-coefficient realization identifies these tensors with the
ringed-site derived tensor. This proves the full-site Tor predicate, including every
nonclassical test sheaf. Independently, lem-sf-proetale-constructible-origin (ii) gives
intrinsic bounded constructibility. Together these prove all of (b). -/
theorem etaleClosedOutput_bounds (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z T W : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (i : Z ⟶ T) [IsClosedImmersion i] [i.IsOver (Spec (.of P.field.k))]
    (j : W ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ)
    (c : ℕ) (_hc : Scheme.HasOpenComplementCondition P.Coefficient j c)
    (K : Etale.DerivedCategoryModule P.Coefficient T)
    (_hK : Etale.DerivedCategory.isBoundedConstructible P.Coefficient T K)
    (r s : ℤ) (_hrs : r ≤ s) :
    (_root_.DerivedCategory.homologyConcentratedIn r s K →
      (Etale.DerivedCategory.isBoundedConstructible P.Coefficient Z
          ((R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint.obj K) ∧
        _root_.DerivedCategory.homologyConcentratedIn r (s + (c : ℤ) + 1)
          ((R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint.obj K)) ∧
      WeilConjectures.constructibleInterval
        P.coefficients.l P.extension P.level P.level_pos Z r (s + (c : ℤ) + 1)
        ((finiteCoefficientIntrinsicDerivedComparison Z P.Ring).obj
          ((R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint.obj K))) ∧
    (Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T r s K →
      (Etale.DerivedCategory.isBoundedConstructible P.Coefficient Z
          ((R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint.obj K) ∧
        Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient Z r (s + (c : ℤ) + 1)
          ((R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint.obj K)) ∧
      Scheme.intrinsicFiniteTorsionConstructible
        P.coefficients.l P.extension P.level P.level_pos Z
        ((finiteCoefficientIntrinsicDerivedComparison Z P.Ring).obj
          ((R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint.obj K)) ∧
      Scheme.HasProEtaleTorAmplitude Z P.Ring
        ((finiteCoefficientIntrinsicDerivedComparison Z P.Ring).obj
          ((R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint.obj K))
        r (s + (c : ℤ) + 1)) := by
  classical
  let : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  let : Finite P.Coefficient := Finite.of_equiv P.Ring Equiv.ulift.symm
  let Q := (R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint.obj K
  let F := finiteCoefficientIntrinsicComparison Z P.Ring
  have eH (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
      (q : ℤ) := (_root_.DerivedCategory.homologyFunctor _ q).mapIso
    ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) j).rightDerivedFunctorPlusCompatibility.app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj M))
  have hcd : ∀ (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
      (q : ℤ), (c : ℤ) < q → IsZero
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) j)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M))) := by
    intro M q hq
    exact (_hc.1 M q hq).of_iso (eH M q).symm
  have hcons : ∀ (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
      (q : ℤ), Scheme.IsConstructibleEtaleModuleSheaf M →
      Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) j)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M))) := by
    intro M q hM
    have he {X Y : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)}
        (e : X ≅ Y) (hX : Scheme.IsConstructibleEtaleModuleSheaf X) :
        Scheme.IsConstructibleEtaleModuleSheaf Y := by
      let : Scheme.IsConstructibleSheaf X :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf X).mp hX
      exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf Y).mpr
        (Scheme.IsConstructibleSheaf.of_iso e)
    exact he (eH M q) (_hc.2 M q hM)
  have hcoh (hKint : _root_.DerivedCategory.homologyConcentratedIn r s K) :
      Etale.DerivedCategory.isBoundedConstructible P.Coefficient Z Q ∧
      _root_.DerivedCategory.homologyConcentratedIn r (s + (c : ℤ) + 1) Q := by
    obtain ⟨hb, hc⟩ :=
      (Etale.closedImmersion_rightAdjoint_amplitude P.Coefficient i j _hij
        r s c (by omega) hcd).2 hcons K hKint _hK.1
    refine ⟨⟨hc, r, s + (c : ℤ) + 1, by omega, ?_⟩, hb⟩
    intro q hq
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff Q r).mp hb.1 q hq
    · exact (_root_.DerivedCategory.isLE_iff Q (s + (c : ℤ) + 1)).mp hb.2 q hq
  have hcompare (hQ : Etale.DerivedCategory.isBoundedConstructible P.Coefficient Z Q) :
      Scheme.intrinsicFiniteTorsionConstructible
        P.coefficients.l P.extension P.level P.level_pos Z
        ((finiteCoefficientIntrinsicDerivedComparison Z P.Ring).obj Q) := by
    have ho := (Scheme.finiteRing_constructibleDerived_origin Z P.Ring).2.2.1 _ |>.mp
      ⟨⟨Q, hQ⟩, ⟨Iso.refl _⟩⟩
    refine ⟨?_, ho.1⟩
    obtain ⟨a, b, _, hz⟩ := ho.2
    apply (Set.finite_Icc a b).subset
    intro q hq
    constructor <;> by_contra h
    · exact hq (hz q (.inl (lt_of_not_ge h)))
    · exact hq (hz q (.inr (lt_of_not_ge h)))
  constructor
  · intro hKint
    obtain ⟨hQ, hb⟩ := hcoh hKint
    refine ⟨⟨hQ, hb⟩, hcompare hQ, ?_⟩
    have hp := F.homologyConcentratedIn_mapDerivedCategory_obj hb
    intro q hq
    constructor <;> by_contra h
    · exact hq ((_root_.DerivedCategory.isGE_iff _ r).mp hp.1 q (lt_of_not_ge h))
    · exact hq ((_root_.DerivedCategory.isLE_iff _ (s + (c : ℤ) + 1)).mp hp.2 q
        (lt_of_not_ge h))
  · intro hTor
    let l := P.coefficients.l
    let E := P.extension
    let n := P.level
    let r₀ : P.Ring := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
      (Padic.coefficientExtensionUniformizer l E)
    have hr₀ : r₀ ^ n = 0 := by
      change (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
        (Padic.coefficientExtensionUniformizer l E)) ^ n = 0
      rw [← map_pow]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]
      exact Ideal.subset_span (Set.mem_singleton _)
    have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
    have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
    have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
        Padic.coefficientExtensionMaximalIdeal l E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    let : (Ideal.span {Padic.coefficientExtensionUniformizer l E}).IsMaximal :=
      hgen ▸ hmax
    have hm := Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n))
      (m := Ideal.span {Padic.coefficientExtensionUniformizer l E})
      Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]
        exact Ideal.pow_le_self (by have := P.level_pos; dsimp [n]; omega))
    have hm₀ : (Ideal.span {r₀}).IsMaximal := by
      change (Ideal.span {(Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
        (Padic.coefficientExtensionUniformizer l E))}).IsMaximal
      simpa only [r₀, Ideal.map_span, Set.image_singleton] using hm
    let ρ : P.Coefficient := ULift.up r₀
    have hρ : IsNilpotent ρ := ⟨n, by
      apply ULift.down_injective
      exact hr₀⟩
    let : (Ideal.span {ρ}).IsMaximal := ulift_span_isMaximal P.Ring r₀ hm₀
    let N : ModuleCat.{u + 1} P.Coefficient :=
      ModuleCat.of P.Coefficient (P.Coefficient ⧸ Ideal.span {ρ})
    let : Finite N := Finite.of_surjective _ (Ideal.Quotient.mk_surjective)
    have hQ := Etale.closed_support_boundedConstructible_torAmplitude P.Coefficient N
      (fun S a b L _ ↦ Etale.residue_test P.Coefficient S ρ hρ a b L)
      i j _hij r s c (by omega) hcd hcons K _hK hTor
    refine ⟨hQ, hcompare hQ.1, ?_⟩
    let Kplus : _root_.DerivedCategory.Plus
        (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
      ⟨Q, by
        obtain ⟨a, b, _, hz⟩ := hQ.1.2
        exact ⟨a, (_root_.DerivedCategory.isGE_iff Q a).mpr
          (fun q hq ↦ hz q (.inl hq))⟩⟩
    have ht := (comparison_torAmplitudeIn_iff P.Ring Z r (s + (c : ℤ) + 1)
      (by omega) Kplus).mp hQ.2
    let ν := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z
    let G := finiteCoefficientIntrinsicRealization Z P.Ring
    let : G.Additive := finiteCoefficientIntrinsicRealization_additive Z P.Ring
    let : PreservesFiniteLimits G :=
      finiteCoefficientIntrinsicRealization_preservesFiniteLimits Z P.Ring
    let : PreservesFiniteColimits G :=
      finiteCoefficientIntrinsicRealization_preservesFiniteColimits Z P.Ring
    have ec : (finiteCoefficientIntrinsicDerivedComparison Z P.Ring).obj Q ≅
        G.mapDerivedCategory.obj (ν.mapDerivedCategory.obj Q) :=
      (Functor.mapDerivedCategoryCompIso ν G).app Q
    have ep := G.mapDerivedCategory.mapIso (ν.mapDerivedCategoryPlusCompatibility.app Kplus)
    refine ⟨ht.1, ?_⟩
    intro L B hL f hf hB M q hq
    exact ht.2 L B (hL.map (fun e ↦ e ≪≫ ec ≪≫ ep.symm)) f hf hB M q hq

end AlgebraicGeometry.ProEtale
