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

private theorem ordinaryComparison_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} (B : Word W location a) :
    B.ordinaryR l E o K = properOpenOrdinaryR l E location o K B := by
  induction B with
  | input k => rfl
  | unit a => rfl
  | tensor B C ihB ihC =>
    simpa only [Word.ordinaryR, properOpenOrdinaryR, ihB, ihC] using
      (show (tensorOrdinaryR l E o _).app _ ≫ _ =
        (ordinaryTensorReductionY9 l E o.ringed _).app _ ≫ _ from rfl)
  | pull f hs ht hq B ih =>
    simp only [Word.ordinaryR, properOpenOrdinaryR, ih]
  | push f hs ht hq hp B ih =>
    simp only [Word.ordinaryR, properOpenOrdinaryR, ih]
    rfl
  | «open» j hj hq B ih =>
    simp only [Word.ordinaryR, properOpenOrdinaryR, ih]

/-- Open constructor equation for proper/open completion transport.
Source: the recursive completion comparison in
`fix-prop-coherence.proof.md`, constructor case `open`.
The proof expands this single constructor using the normalized operation comparison,
naturality, and the admissibility hypotheses for its immediate children.
(blueprint: lem-sf-proper-open-lambda-completion-transport-open) -/
theorem properOpenLambdaCompletionTransport_open
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
    {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
    (hq : QuasiCompact j) (B : Word W location a)
    (hLength : (Word.open j hj hq B).length ≤ 3)
    (hAdmissible : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.open j hj hq B)) :
    (IntegralSystemRealization.calculus Cf.l E (W b)).reduction.map
        ((Word.open j hj hq B).completionMap Cf.l E W location o K) ≫
      (Word.open j hj hq B).r Cf.l E W location o K =
      properOpenOrdinaryR Cf.l E location o K (Word.open j hj hq B) := by
  have h := word_completion_reduction Cf.l E o K lo hi torLo torHi hInputs
    (Word.open j hj hq B) hLength hAdmissible
  exact h.trans (ordinaryComparison_eq Cf.l E o W location K (Word.open j hj hq B))

end WeilConjectures.OpenInterchangeReduction
