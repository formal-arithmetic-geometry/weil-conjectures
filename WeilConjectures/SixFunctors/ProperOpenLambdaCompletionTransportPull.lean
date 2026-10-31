/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProperOpenLambdaOrdinarySquare
import WeilConjectures.SixFunctors.PrimitiveQuotientAugmentations
import WeilConjectures.SixFunctors.ProperOpenLambdaCompletionTransportTensor
import WeilConjectures.SixFunctors.ProperOpenLambdaCompletionTransportPush
import WeilConjectures.SixFunctors.ProperOpenLambdaCompletionTransportOpen

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u s i
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction

/-- Pull constructor equation for proper/open completion transport.
Source: the recursive completion comparison in
`fix-prop-coherence.proof.md`, constructor case `pull`.
The proof expands this single constructor using the normalized operation comparison,
naturality, and the admissibility hypotheses for its immediate children.
(blueprint: lem-sf-proper-open-lambda-completion-transport-pull) -/
theorem properOpenLambdaCompletionTransport_pull
    {D : FiniteFieldDatum.{u}} (Cf : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic Cf.l) E]
    [FiniteDimensional (Padic Cf.l) E] (o : Operations Cf.l E)
    {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource Cf.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hInputs : ∀ k : I, Admissible Cf.l E
      (IntegralSystemRealization.calculus Cf.l E (W (location k))) (K k)
      lo hi torLo torHi)
    {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
    (ht : LocallyOfFiniteType f) (hq : QuasiCompact f)
    (B : Word W location b)
    (hLength : (Word.pull f hs ht hq B).length ≤ 3)
    (hAdmissible : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.pull f hs ht hq B)) :
    (IntegralSystemRealization.calculus Cf.l E (W a)).reduction.map
        ((Word.pull f hs ht hq B).completionMap Cf.l E W location o K) ≫
      (Word.pull f hs ht hq B).r Cf.l E W location o K =
      properOpenOrdinaryR Cf.l E location o K (Word.pull f hs ht hq B) := by
  have pull_step {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
      (ht : LocallyOfFiniteType f) (hq : QuasiCompact f) (B : Word W location b)
      (hB : (IntegralSystemRealization.calculus Cf.l E (W b)).reduction.map
          (B.completionMap Cf.l E W location o K) ≫ B.r Cf.l E W location o K =
        properOpenOrdinaryR Cf.l E location o K B) :
      (IntegralSystemRealization.calculus Cf.l E (W a)).reduction.map
          ((Word.pull f hs ht hq B).completionMap Cf.l E W location o K) ≫
        (Word.pull f hs ht hq B).r Cf.l E W location o K =
      properOpenOrdinaryR Cf.l E location o K (Word.pull f hs ht hq B) := by
    have hunit := (primitiveQuotientAugmentations Cf.l E o.ringed o.system
      o.realization).2 f (B.integralValue Cf.l E W location o K)
    have := hunit.1
    have hinv : inverseOrZero
        ((IntegralSystemRealization.calculus Cf.l E (W a)).reduction.map
          (((o.ringed.pull f).unit Cf.l E).app
            (B.integralValue Cf.l E W location o K))) = inv
        ((IntegralSystemRealization.calculus Cf.l E (W a)).reduction.map
          (((o.ringed.pull f).unit Cf.l E).app
            (B.integralValue Cf.l E W location o K))) := by
      unfold inverseOrZero
      split <;> simp_all
    dsimp only [Word.completionMap, Word.r, properOpenOrdinaryR, pullR]
    rw [Functor.map_comp, hinv]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    have hn := (o.realization.reductionPull f).hom.naturality
      (B.completionMap Cf.l E W location o K)
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, hB]
  have hchild : (IntegralSystemRealization.calculus Cf.l E (W b)).reduction.map
        (B.completionMap Cf.l E W location o K) ≫ B.r Cf.l E W location o K =
      properOpenOrdinaryR Cf.l E location o K B := by
    have hlen : B.length ≤ 3 := by simp only [Word.length] at hLength; omega
    have had := hAdmissible.2
    clear hLength hAdmissible hs ht hq f
    induction B with
    | input k => simp [Word.completionMap, Word.r, properOpenOrdinaryR]
    | unit a => simp [Word.completionMap, Word.r, properOpenOrdinaryR]
    | tensor B C ihB ihC =>
      exact properOpenLambdaCompletionTransport_tensor Cf E o W location K lo hi torLo torHi
        hInputs B C hlen had
    | pull g hsg htg hqg B ih =>
      exact pull_step g hsg htg hqg B (ih (by simp only [Word.length] at hlen; omega) had.2)
    | push g hsg htg hqg hpg B ih =>
      exact properOpenLambdaCompletionTransport_push Cf E o W location K lo hi torLo torHi
        hInputs g hsg htg hqg hpg B hlen had
    | «open» j hj hqj B ih =>
      exact properOpenLambdaCompletionTransport_open Cf E o W location K lo hi torLo torHi
        hInputs j hj hqj B hlen had
  exact pull_step f hs ht hq B hchild

end WeilConjectures.OpenInterchangeReduction
