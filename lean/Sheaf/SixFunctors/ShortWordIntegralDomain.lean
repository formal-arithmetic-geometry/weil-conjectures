/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T7
-/
module

public import Sheaf.SixFunctors.GeneratorReductionData
public import Sheaf.Paper.FiniteSystemPullbackCoherence
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import all Sheaf.SixFunctors.OpenReconstructionEffectivity

/-! # Integral intermediate domains

Source: current blueprint fix-prop-coherence, primitive realization step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def reduction_iso (X : Scheme.{u})
    (M : coefficientSequenceDerived l E X) (hM : IsNormalizedCoefficientSequence l E X M)
    (A : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (e : A ≅ (coefficientSequenceLimit l E X).obj M) :
    (IntegralSystemRealization.calculus l E X).reduction.obj A ≅ M := by
  have := ((purNormalizedReconstructionOfScheme l E X
    (IntegralSystemRealization.calculus l E X)).1 M hM).2
  exact (IntegralSystemRealization.calculus l E X).reduction.mapIso e ≪≫
    asIso ((IntegralSystemRealization.calculus l E X).adjunction.counit.app M)

private theorem domain_of_realization (X : Scheme.{u})
    (M : coefficientSequenceDerived l E X) (lo hi torLo torHi : ℤ)
    (hM : SystemAdmissible l E X M lo hi torLo torHi)
    (A : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (e : A ≅ (coefficientSequenceLimit l E X).obj M) :
    finiteTorConstructibleIntegral l E X A := by
  have hcomplete := ((purNormalizedReconstructionOfScheme l E X
    (IntegralSystemRealization.calculus l E X)).1 M hM.1).1
  obtain ⟨D, hl, hA⟩ := complete_of_iso l E X e.symm hcomplete
  have hc : IsSfDerivedComplete l E X A :=
    (sfDerivedComplete_iff_legacy l E X D hl A).2 hA
  have r := reduction_iso l E X M hM.1 A e
  have d (n : ℕ) : (scalarReductionDerivedExtension.{u, u} l E X n).obj A ≅
      (coefficientSequenceDerivedEvaluation l E X n).obj M :=
    ((IntegralSystemRealization.calculus l E X).reductionEvaluation n).symm.app A ≪≫
      (coefficientSequenceDerivedEvaluation l E X n).mapIso r
  have hlevels := hM.2.2.2.2
  refine ⟨⟨hc, lo, hi, hM.2.2.1, fun n ↦ ?_⟩,
    torLo, torHi, hM.2.2.2.1, fun n ↦ ?_⟩
  · let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    have : ObjectProperty.IsClosedUnderIsomorphisms
        (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X) :=
      (proEtale_bounded_constructible_isTriangulated X
        (Padic.coefficientExtensionRing l E (n + 1))).1
    refine ⟨(intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).prop_of_iso
      (d n).symm (hlevels n).1, ?_⟩
    intro q hq
    apply (hlevels n).2.1
    intro hz
    exact hq (hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso (d n)))
  · refine ⟨(hlevels n).2.2.1, ?_⟩
    rintro L P ⟨q⟩ f hf hP N i hi
    exact (hlevels n).2.2.2 L P ⟨q ≪≫ d n⟩ f hf hP N i hi

private theorem word_system_admissible
    {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)
    (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ) {a : S} (B : Word W location a)
    (hB : Word.admissible l E W location o K lo hi torLo torHi B) :
    SystemAdmissible l E (W a)
      (B.systemValue l E W location o (inputReduction l E W location K))
      lo hi torLo torHi := by
  cases B <;> exact hB.1

private theorem word_realization
    {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)
    (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    {a : S} (B : Word W location a)
    (hB : Word.admissible l E W location o K lo hi torLo torHi B) :
    Nonempty (B.integralValue l E W location o K ≅
      (coefficientSequenceLimit l E (W a)).obj
        (B.systemValue l E W location o (inputReduction l E W location K))) := by
  induction B with
  | input k =>
      have hc := (hAdm k).1.1.1
      obtain ⟨D, hl⟩ := exists_coefficientTestDatum l
      have hu := (purNormalizedReconstructionOfScheme l E (W (location k))
        (IntegralSystemRealization.calculus l E (W (location k)))).2 (K k)
        ⟨D, hl, (sfDerivedComplete_iff_legacy l E _ D hl _).1 hc⟩
      exact ⟨asIso ((IntegralSystemRealization.calculus l E _).adjunction.unit.app (K k))⟩
  | unit a =>
      have hu := (purNormalizedReconstructionOfScheme l E (W a)
        (IntegralSystemRealization.calculus l E (W a))).2 _ (tensorUnit_complete l E (W a))
      exact ⟨asIso ((IntegralSystemRealization.calculus l E _).adjunction.unit.app _) ≪≫
        (coefficientSequenceLimit l E (W a)).mapIso (o.unitReduction (W a))⟩
  | @tensor a B C ihB ihC =>
      obtain ⟨eB⟩ := ihB hB.2.1
      obtain ⟨eC⟩ := ihC hB.2.2
      have hsysB := word_system_admissible l E W location o K lo hi torLo torHi B hB.2.1
      let rB := reduction_iso l E (W a) _ hsysB.1 _ eB
      have hsysC := word_system_admissible l E W location o K lo hi torLo torHi C hB.2.2
      let rC := reduction_iso l E (W a) _ hsysC.1 _ eC
      exact ⟨(tensorD l E (W a)).symm.app _ ≪≫
        (coefficientSequenceLimit l E (W a)).mapIso
          ((IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.mapIso
            (Iso.prod rB rC))⟩
  | @pull a b f hs ht hq B ih =>
      obtain ⟨eB⟩ := ih hB.2
      have hsysB := word_system_admissible l E W location o K lo hi torLo torHi B hB.2
      let rB := reduction_iso l E (W b) _ hsysB.1 _ eB
      exact ⟨(pullD l E f).symm.app _ ≪≫
        (coefficientSequenceLimit l E (W a)).mapIso
          ((IntegralSystemRealization.pull l E f).mapIso rB)⟩
  | @push a b f hs ht hq hp B ih =>
      obtain ⟨eB⟩ := ih hB.2
      have hsysB := word_system_admissible l E W location o K lo hi torLo torHi B hB.2
      let rB := reduction_iso l E (W a) _ hsysB.1 _ eB
      exact ⟨(coefficientSequenceLimit l E (W b)).mapIso
        ((IntegralSystemRealization.Operations.push l E o.system f).mapIso rB)⟩
  | @«open» a b j hj hq B ih =>
      let := hj
      let := hq
      obtain ⟨eB⟩ := ih hB.2
      have hsys := word_system_admissible l E W location o K lo hi torLo torHi B hB.2
      have hdom := domain_of_realization l E (W a) _ lo hi torLo torHi hsys _ eB
      obtain ⟨hr, hu⟩ := openReconstructionEffectivity l E o.system o.realization j
        (B.integralValue l E W location o K) (Or.inl hdom)
      let rB := reduction_iso l E (W a) _ hsys.1 _ eB
      exact ⟨asIso ((IntegralSystemRealization.calculus l E (W b)).adjunction.unit.app _) ≪≫
        (coefficientSequenceLimit l E (W b)).mapIso
          ((asIso ((o.realization.openReduction l E j).app _)).symm ≪≫
            (IntegralSystemRealization.Operations.shriek l E o.system j).mapIso rB)⟩

/-- Constructibility and finite Tor amplitude of the integral vertices needed as
children of a word of length at most three. The scalar unit is allowed explicitly.
Source: blueprint fix-prop-coherence, input and intermediate restrictions, and
realization steps 1--3; Stacks 099M and 099N
(blueprint: lem-sf-short-word-integral-domain).

Proof: induct on the word, using the recursively supplied intermediate systems.
An input satisfies the first conjunct of Admissible; the unit satisfies the second
alternative. A completed tensor or pullback is the actual limit of its strict
quotient operation system by its defining quotient-tower comparison. Proper image
is that limit by definition. The given normalized systems, compatible etale origins,
constructible reductions and common cohomological bounds give constructibility of
these limits by normalized reconstruction. The same reconstruction identifies each
finite reduction with the corresponding system level, so the supplied common Tor
interval proves finite Tor amplitude. For an open extension use the actual open
reduction mate and the open reconstruction comparison: extension by zero preserves
completeness and constructibility, while its finite reduction is the given strict
open-extension system. For a scalar-unit child use its rank-one free model in
these comparisons. The identity morphism and empty open are included. Only a
child word of length at most two is needed; no claim about unrelated words or
uniform preservation of normalized systems is used. -/
theorem shortWordIntegralDomain
    {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)
    (o : Operations l E) {a : S} (B : Word W location a) (hLength : B.length ≤ 2)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    (hIntermediate : Word.admissible l E W location o K lo hi torLo torHi B) :
    finiteTorConstructibleIntegral l E (W a) (B.integralValue l E W location o K) ∨
      B.integralValue l E W location o K =
        (IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.tensorUnit :=
  by
    have _ := hLength
    obtain ⟨e⟩ := word_realization l E W location o K lo hi torLo torHi hAdm B hIntermediate
    have hsys := word_system_admissible l E W location o K lo hi torLo torHi B hIntermediate
    exact Or.inl (domain_of_realization l E (W a) _ lo hi torLo torHi hsys _ e)

end WeilConjectures.GeneratorReduction
