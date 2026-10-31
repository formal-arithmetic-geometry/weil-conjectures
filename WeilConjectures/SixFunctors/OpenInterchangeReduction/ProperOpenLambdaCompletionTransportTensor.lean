/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.ProperOpenLambdaOrdinarySquare
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares

@[expose] public noncomputable section
set_option autoImplicit false
universe u s i
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction

/-- Tensor constructor equation for proper/open completion transport.
Source: the recursive completion comparison in
`fix-prop-coherence.proof.md`, constructor case `tensor`.
The proof expands this single constructor using the normalized operation comparison,
naturality, and the admissibility hypotheses for its immediate children.
(blueprint: lem-sf-proper-open-lambda-completion-transport-tensor) -/
theorem properOpenLambdaCompletionTransport_tensor
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
    {a : S} (B C : Word W location a)
    (hLength : (Word.tensor B C).length ≤ 3)
    (hAdmissible : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.tensor B C)) :
    (IntegralSystemRealization.calculus Cf.l E (W a)).reduction.map
        ((Word.tensor B C).completionMap Cf.l E W location o K) ≫
      (Word.tensor B C).r Cf.l E W location o K =
      properOpenOrdinaryR Cf.l E location o K (Word.tensor B C) := by
  have hOrdinary {a : S} (A : Word W location a) :
      A.ordinaryR Cf.l E o K = properOpenOrdinaryR Cf.l E location o K A := by
    induction A with
    | input k => rfl
    | unit a => rfl
    | tensor A B ihA ihB =>
      simpa only [Word.ordinaryR, properOpenOrdinaryR, tensorOrdinaryR,
        ordinaryTensorReductionY9, NatTrans.comp_app, Functor.whiskerRight_app]
        using congrArg₂ (fun f g ↦
          (ordinaryTensorReductionY9 Cf.l E o.ringed _).app
              (A.ringedValue Cf.l E W location o K,
                B.ringedValue Cf.l E W location o K) ≫
            (IntegralSystemRealization.calculus Cf.l E _).systemClosed.tensor.map
              (Prod.mkHom f g)) ihA ihB
    | pull f hs ht hq A ih =>
      simpa only [Word.ordinaryR, properOpenOrdinaryR] using
        congrArg (fun g ↦ (o.realization.reductionPull f).hom.app
          (A.ringedValue Cf.l E W location o K) ≫
          (IntegralSystemRealization.pull Cf.l E f).map g) ih
    | push f hs ht hq hp A ih =>
      simpa only [Word.ordinaryR, properOpenOrdinaryR, pushOrdinaryR,
        ordinaryPushReductionY9] using
        congrArg (fun g ↦ (ordinaryPushReductionY9 Cf.l E o.system o.realization f).app
          (A.ringedValue Cf.l E W location o K) ≫
          (IntegralSystemRealization.Operations.push Cf.l E o.system f).map g) ih
    | «open» j hj hq A ih =>
      let := hj
      simpa only [Word.ordinaryR, properOpenOrdinaryR] using
        congrArg (fun g ↦ inverseOrZero ((o.realization.openReduction Cf.l E j).app
          (A.ringedValue Cf.l E W location o K)) ≫
          (IntegralSystemRealization.Operations.shriek Cf.l E o.system j).map g) ih
  exact (word_completion_reduction Cf.l E o K lo hi torLo torHi hInputs
    (Word.tensor B C) hLength hAdmissible).trans (hOrdinary (Word.tensor B C))

end WeilConjectures.OpenInterchangeReduction
