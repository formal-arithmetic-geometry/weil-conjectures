/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.FormalChartGeometricData
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.RingTheory.FormalMonoidExtensionModel
public import Sheaf.RingTheory.CompleteToricModel
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.TraceFormula.ChartFaceResidualUnitDecomposition
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.AlgebraicGeometry.FormalChartLocalPreparation
import Sheaf.AlgebraicGeometry.ExtendedFormalModelDimensions
import Sheaf.AlgebraicGeometry.FormalChartStrictComparison
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.Data.ENat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Formal chart models and log regularity of geometric stalks

Source: ILO, Travaux de Gabber, VI 1.6 and 1.8, printed p.70; the agent-supplied
formal-model-to-geometric-stalk refinement; Stacks Tags 00MA, 05WS, 07NY, 07NV,
06LN and 06LK (blueprint: lem-trf-formal-chart-geometric-regularity).

Multiplicative monoids represent the additive charts of the node. The helpers
below only name its rings, monomials, model hypotheses and combined conclusions.
Affine coordinate isomorphisms and lifts in the statement are constrained by both
projections, so they specify the canonical tensor coordinates and closed-point lift.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
open FormalChartGeometric

private theorem rank_eq_of_mulEquiv {T U : Type u} [CommMonoid T] [CommMonoid U]
    (e : T ≃* U) : rank T = rank U := by
  let eg : Algebra.GrothendieckGroup T ≃* Algebra.GrothendieckGroup U :=
    (Localization.monoidOf (⊤ : Submonoid T)).mulEquivOfMulEquiv
      (Localization.monoidOf (⊤ : Submonoid U)) (j := e) (by
        ext x
        simp)
  let el : Additive (Algebra.GrothendieckGroup T) ≃ₗ[ℤ]
      Additive (Algebra.GrothendieckGroup U) := eg.toAdditive.toIntLinearEquiv
  exact congrArg (fun c : Cardinal.{u} ↦ (Cardinal.toENat c : WithBot ℕ∞))
    (el.baseChange ℤ ℚ _ _).rank_eq

private theorem regularity_of_model_dimensions
    (B T : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommMonoid T]
    (J : Ideal B) (hJ : J ≤ IsLocalRing.maximalIdeal B) (mixed : Bool)
    (hmodel : ModelDimensions B T J mixed) :
    IsRegularRing (B ⧸ J) ∧ ringKrullDim B = ringKrullDim (B ⧸ J) + rank T := by
  have hJproper : J ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top hJ
  have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJproper
  have : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  obtain ⟨_, _, _, _, _, _, e, _⟩ := AdicCompletion.exists_local_completion_quotient
    B (B ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hmax : (IsLocalRing.maximalIdeal B).map (Ideal.Quotient.mk J) =
      IsLocalRing.maximalIdeal (B ⧸ J) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have ehat : (AdicCompletion (IsLocalRing.maximalIdeal B) B ⧸
      J.map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B))) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal (B ⧸ J)) (B ⧸ J) := by
    rw [Ideal.mk_ker, hmax] at e
    exact e
  obtain ⟨D, hD, hDnontrivial, hDregular, _, hregular, _, hdim, hdimJ⟩ := hmodel
  let := hD
  let := hDnontrivial
  let := hDregular
  let := hregular
  have : IsRegularRing (AdicCompletion (IsLocalRing.maximalIdeal (B ⧸ J)) (B ⧸ J)) :=
    IsRegularRing.of_ringEquiv ehat
  have : IsRegularLocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal (B ⧸ J)) (B ⧸ J)) :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  have : IsRegularLocalRing (B ⧸ J) :=
    (AdicCompletion.isRegularLocalRing_iff (B ⧸ J)).mpr inferInstance
  refine ⟨(IsRegularLocalRing.localization_at_prime_and_isRegularRing
    (IsLocalRing.maximalIdeal (B ⧸ J))).2, ?_⟩
  rw [(RingTheory.completion_dimension B).1] at hdim
  rw [ehat.ringKrullDim, (RingTheory.completion_dimension (B ⧸ J)).1] at hdimJ
  have heq : ringKrullDim B + (if mixed then 1 else 0) =
      (ringKrullDim (B ⧸ J) + rank T) + (if mixed then 1 else 0) := by
    calc
      _ = ringKrullDim D + rank T := hdim
      _ = (ringKrullDim (B ⧸ J) + (if mixed then 1 else 0)) + rank T := by rw [hdimJ]
      _ = _ := by ac_rfl
  cases mixed with
  | false => simpa using heq
  | true => exact (ENat.WithBot.add_one_cancel).mp heq

/-- Formal toric chart models give the asserted completed pairs, regular strata,
dimension identities and canonical geometric strict-local comparison.
Source: ILO VI 1.6 and 1.8, p.70; the agent-supplied refinement; Stacks Tags
00MA, 05WS, 07NY, 07NV, 06LN and 06LK
(blueprint: lem-trf-formal-chart-geometric-regularity).

Proof (the eight steps of the DAG node):
1. Choose a Noetherian affine neighbourhood of the base point. Localization,
   pointed-neighbourhood/triple comparison and the strict-henselization triple theorem
   make A nonzero Noetherian local. Finite generation of Q presents the tensor ring
   C as a finite-type A-algebra, so B is Noetherian. The chosen lift is over the closed
   point of Spec A, hence its prime contracts to m_A and A -> B is local. Each generator
   of J is a nonunit, so J is contained in m_B. The same argument proves Z locally
   Noetherian. Uses pqf-def-locnoeth, localization-noetherian, etale-local-ring-triples,
   strict-henselization-triples, strict-henselization-noetherian and finite-type-Noetherian.
2. Apply chart-face-residual-unit-decomposition: G and F are faces; S and T are sharp
   fs with finite free completions. Retain the free residual unit group K and the unit
   character. The ideal J corresponds exactly to the nonzero T-monomial ideal.
3. Apply formal-monoid-extension-model to these same A, R, Q, h, alpha, a, epsilon
   and prime. It supplies D and the pair isomorphism in each case. In the mixed case
   the reduction of eta is in m_D but outside m_D squared. No untwisted identification
   of individual Q-monomials with T-monomials is asserted.
4. Apply formal-monoid-ring-dimension. In the field case the stratum is D; in the
   mixed case it is D/(eta-bar), regular because eta-bar is a parameter. This proves
   the two completed dimension formulas with e = 0 or 1 and regularity of the stratum.
5. J lies in m_B, so B/J is nonzero Noetherian local. Completion-of-quotient gives
   its completion as Bhat/JBhat. Completion detects regularity and preserves both
   dimensions, giving regularity of B/J and dim B = dim(B/J) + rank T^gp.
6. The canonical Spec A -> W is ind-etale on affine charts. Ind-etale strict-local
   invariance applied after base change gives the canonical isomorphism over Z.
   Pointed-neighbourhood/triple comparison identifies the affine strict local ring
   with B^sh for the separable residue closure inside the SAME Omega. The comparison
   is over Z and therefore respects every chart monomial.
7. The local faithfully flat map B -> B^sh reflects units, so the chart face remains F.
   Chart-face logification identifies the characteristic with T. A nonunit log germ
   is a nonface chart monomial times a ring unit, so its ideal is exactly JB^sh.
8. Strict henselization commutes with the surjection B -> B/J (Stacks 05WS). It
   preserves regularity of B/J and dimensions of B and B/J (06LN, 06LK). Transport
   these results through Step 6 and the characteristic and ideal identifications of
   Step 7: these are precisely the two conditions defining log regularity at z.
The argument includes n=0, T trivial, empty chart boundary, and the field case.
-/
theorem formal_chart_geometric_regularity
    (W : FineSaturatedLogScheme.{u})
    (R Q : Type u) [CommMonoid R] [CommMonoid Q]
    (_hR : IsFineSaturatedMonoid R) (_hQ : IsFineSaturatedMonoid Q)
    (β : R →* W.logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W.scheme))))
    (_hβ : W.logStructure.IsChart (Scheme.Etale.mk (𝟙 W.scheme)) β)
    (y : W.scheme ⟶ Spec (.of (MonoidAlgebra ℤ R)))
    (_hy : ∀ r : R, y.appTop ((Scheme.ΓSpecIso (.of (MonoidAlgebra ℤ R))).inv
      (MonoidAlgebra.single r 1)) =
        W.logStructure.alpha.app (op (Scheme.Etale.mk (𝟙 W.scheme))) (β r))
    (h : R →* Q)
    (_hgp : Function.Bijective (Algebra.ChartResidual.groupMap h))
    (N : EtaleLogStructure (chartScheme y h))
    (γ : Q →* N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (chartScheme y h)))))
    (_hγ : N.IsChart (Scheme.Etale.mk (𝟙 (chartScheme y h))) γ)
    (_hγmap : ∀ q : Q,
      (pullback.snd y (toricMap h)).appTop
          ((Scheme.ΓSpecIso (.of (MonoidAlgebra ℤ Q))).inv (MonoidAlgebra.single q 1)) =
        N.alpha.app (op (Scheme.Etale.mk (𝟙 (chartScheme y h)))) (γ q))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ chartScheme y h)
    (zA : Spec (.of Ω) ⟶ pullback (baseMap y h z) (pullback.fst y (toricMap h)))
    (_hzA : zA ≫ pullback.snd (baseMap y h z) (pullback.fst y (toricMap h)) = z)
    (_hzAclosed : zA ≫ pullback.fst (baseMap y h z) (pullback.fst y (toricMap h)) =
      Spec.map (Scheme.strictHenselizationEval (z ≫ pullback.fst y (toricMap h))))
    (eC : Spec (Algebra.monoidChartTensor (alpha y h z) h) ≅
      pullback (baseMap y h z) (pullback.fst y (toricMap h)))
    (_heCA : eC.hom ≫ pullback.fst (baseMap y h z) (pullback.fst y (toricMap h)) =
      Spec.map (CommRingCat.ofHom (Algebra.monoidChartTensorBase (alpha y h z) h)))
    (_heCQ : eC.hom ≫ pullback.snd (baseMap y h z) (pullback.fst y (toricMap h)) ≫
        pullback.snd y (toricMap h) =
      Spec.map (CommRingCat.ofHom (tensorRight (alpha y h z) h)))
    (q : Ideal (Algebra.monoidChartTensor (alpha y h z) h)) [q.IsPrime]
    (_hq : q = (Scheme.SpecToEquivOfField Ω _ (zA ≫ eC.inv)).1.asIdeal)
    (_hface : (Algebra.ChartResidual.targetFace (alpha y h z) h q).comap h =
      Algebra.ChartResidual.sourceFace (alpha y h z))
    (a : Multiplicative (Algebra.chartSharpMonoid (alpha y h z)) →* baseRing y h z)
    (_hasharp : ∀ s, IsUnit (a s) ↔ s = 1)
    (ε : Algebra.GrothendieckGroup R →* (baseRing y h z)ˣ)
    (_hα : ∀ r : Localization ((IsUnit.submonoid (baseRing y h z)).comap (alpha y h z)),
      Algebra.localizedUnitChart (alpha y h z) r =
        (ε (Algebra.unitChartGroupMap (alpha y h z) r) : baseRing y h z) *
          a (Multiplicative.ofAdd (Additive.ofMul (Associates.mk r))))
    (tB : Spec (.of Ω) ⟶ Spec (.of (Localization.AtPrime q)))
    (_htB : tB ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (Algebra.monoidChartTensor (alpha y h z) h) (Localization.AtPrime q))) =
        zA ≫ eC.inv)
    (mixed : Bool)
    (_hmodel : HasCompletion (baseRing y h z) (alpha y h z) a mixed) :
    ModelDimensions (Localization.AtPrime q)
      (Algebra.ChartResidual.targetSharp (alpha y h z) h q)
      (Algebra.localizedTensorBoundary (alpha y h z) h q) mixed ∧
    IsRegularRing (Localization.AtPrime q ⧸
      Algebra.localizedTensorBoundary (alpha y h z) h q) ∧
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime q ⧸
        Algebra.localizedTensorBoundary (alpha y h z) h q) +
      rank (Algebra.ChartResidual.targetSharp (alpha y h z) h q) ∧
    IsIso (Scheme.strictHenselizationMap
      (pullback.snd (baseMap y h z) (pullback.fst y (toricMap h))) zA) ∧
    (∃ e : strictLocalRing (chartScheme y h) z ≃+* Scheme.strictHenselization tB,
      (∀ (U : (chartScheme y h).Etale) (v : (Scheme.pointSmallEtale z).fiber.obj U),
        ∃ k : Scheme.strictLocalization tB ⟶ U.left,
          k ≫ U.hom = Scheme.strictLocalizationToBase tB ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap (Algebra.monoidChartTensor (alpha y h z) h)
                (Localization.AtPrime q))) ≫ eC.hom ≫
                  pullback.snd (baseMap y h z) (pullback.fst y (toricMap h)) ∧
          Spec.map (Scheme.strictHenselizationEval tB) ≫ k = v.left ∧
          ∀ c : Γ(U.left, ⊤),
            e (strictLocalGerm (chartScheme y h) z U v c) =
              (Scheme.ΓSpecIso (Scheme.strictHenselization tB)).hom (k.appTop c)) ∧
      (∀ v : Q,
        e (N.toEtalePrelogStructure.stalkAlpha z
          (N.toEtalePrelogStructure.germ z (Scheme.Etale.mk (𝟙 (chartScheme y h)))
            (Over.homMk z) (γ v))) =
          strictBase tB (Algebra.localizedTensorMonomial (alpha y h z) h q v)) ∧
      (N.nonunitIdeal z).map e.toRingHom =
        strictIdeal tB (Algebra.localizedTensorBoundary (alpha y h z) h q)) ∧
    (∃ eT : N.characteristic z ≃* Algebra.ChartResidual.targetSharp (alpha y h z) h q,
      ∀ v : Q,
        eT (Associates.mk (N.toEtalePrelogStructure.germ z
          (Scheme.Etale.mk (𝟙 (chartScheme y h))) (Over.homMk z) (γ v))) =
            Algebra.ChartResidual.sharpMap
              (Algebra.ChartResidual.targetFace (alpha y h z) h q) v) ∧
    (∃ tJ : Spec (.of Ω) ⟶ Spec (.of (Localization.AtPrime q ⧸
        Algebra.localizedTensorBoundary (alpha y h z) h q)),
      tJ ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Algebra.localizedTensorBoundary (alpha y h z) h q))) = tB ∧
      ∃ eJ : (Scheme.strictHenselization tB ⧸
          strictIdeal tB (Algebra.localizedTensorBoundary (alpha y h z) h q)) ≃+*
            Scheme.strictHenselization tJ,
        ∀ b : Localization.AtPrime q,
          eJ (Ideal.Quotient.mk _ (strictBase tB b)) =
            strictBase tJ (Ideal.Quotient.mk _ b)) ∧
    IsRegularRing (Scheme.strictHenselization tB ⧸
      strictIdeal tB (Algebra.localizedTensorBoundary (alpha y h z) h q)) ∧
    ringKrullDim (Scheme.strictHenselization tB) =
      ringKrullDim (Scheme.strictHenselization tB ⧸
        strictIdeal tB (Algebra.localizedTensorBoundary (alpha y h z) h q)) +
      rank (Algebra.ChartResidual.targetSharp (alpha y h z) h q) ∧
    IsRegularRing (strictLocalRing (chartScheme y h) z ⧸ N.nonunitIdeal z) ∧
    ringKrullDim (strictLocalRing (chartScheme y h) z) =
      ringKrullDim (strictLocalRing (chartScheme y h) z ⧸ N.nonunitIdeal z) +
        (N.characteristicRank z : WithBot ℕ∞) := by
  obtain ⟨hA, hB, hcontract⟩ := formal_chart_local_preparation W R Q _hQ y h z zA
    _hzA _hzAclosed eC _heCA q _hq
  let := hA
  let := hB
  have hJ : Algebra.localizedTensorBoundary (alpha y h z) h q ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    apply Ideal.span_le.mpr
    rintro b ⟨v, hv, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).mpr hv
  obtain ⟨_, _, _, _, _, _, hfsT, _, hsharpT, _⟩ :=
    Algebra.chart_face_residual_unit_decomposition
      (baseRing y h z) R Q _hR _hQ h _hgp (alpha y h z) a ε _hα q hcontract
  have hmodels := Algebra.formalMonoidExtension_model
    (baseRing y h z) R Q _hR _hQ h _hgp (alpha y h z) a ε _hα q hcontract
  have hmodel : AddMonoidAlgebra.HasExtendedFormalMonoidModel (Localization.AtPrime q)
      (Additive (Algebra.ChartResidual.targetSharp (alpha y h z) h q))
      (Algebra.localizedTensorBoundary (alpha y h z) h q) mixed := by
    cases mixed with
    | false => exact hmodels.1 _hmodel
    | true => exact hmodels.2 _hmodel
  have hcompleted := extended_formal_model_dimensions
    (Localization.AtPrime q) (Algebra.ChartResidual.targetSharp (alpha y h z) h q)
    hfsT hsharpT (Algebra.localizedTensorBoundary (alpha y h z) h q) hJ mixed hmodel
  obtain ⟨hregular, hdimension⟩ := regularity_of_model_dimensions
    (Localization.AtPrime q) (Algebra.ChartResidual.targetSharp (alpha y h z) h q)
    (Algebra.localizedTensorBoundary (alpha y h z) h q) hJ mixed hcompleted
  obtain ⟨hiso, he, heT, heJ, hascent, hdimB, hdimJ⟩ :=
    formal_chart_strict_comparison W R Q _hQ y h N γ _hγ _hγmap z zA
      _hzA _hzAclosed eC _heCA _heCQ q _hq _hface tB _htB
  have hstrictRegular := hascent hregular
  have hstrictDimension : ringKrullDim (Scheme.strictHenselization tB) =
      ringKrullDim (Scheme.strictHenselization tB ⧸
        strictIdeal tB (Algebra.localizedTensorBoundary (alpha y h z) h q)) +
      rank (Algebra.ChartResidual.targetSharp (alpha y h z) h q) := by
    rw [hdimB, hdimJ]
    exact hdimension
  obtain ⟨e, hpointed, hmonomial, hideal⟩ := he
  obtain ⟨eT, hchart⟩ := heT
  let eQ := Ideal.quotientEquiv (N.nonunitIdeal z)
    (strictIdeal tB (Algebra.localizedTensorBoundary (alpha y h z) h q)) e hideal.symm
  have hstalkRegular : IsRegularRing
      (strictLocalRing (chartScheme y h) z ⧸ N.nonunitIdeal z) := by
    let := hstrictRegular
    exact IsRegularRing.of_ringEquiv eQ.symm
  have hrank : (N.characteristicRank z : WithBot ℕ∞) =
      rank (Algebra.ChartResidual.targetSharp (alpha y h z) h q) :=
    rank_eq_of_mulEquiv eT
  refine ⟨hcompleted, hregular, hdimension, hiso,
    ⟨e, hpointed, hmonomial, hideal⟩, ⟨eT, hchart⟩, heJ,
    hstrictRegular, hstrictDimension, hstalkRegular, ?_⟩
  rw [e.ringKrullDim, eQ.ringKrullDim, hrank]
  exact hstrictDimension

end AlgebraicGeometry
