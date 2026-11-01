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

end WeilConjectures.OpenInterchangeReduction
