/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProperOpenLambdaOrdinarySquare
import WeilConjectures.SixFunctors.ProperOpenLambdaCompletionTransportTensor
import WeilConjectures.SixFunctors.ProperOpenLambdaCompletionTransportPull
import WeilConjectures.SixFunctors.ProperOpenLambdaCompletionTransportPush
import WeilConjectures.SixFunctors.ProperOpenLambdaCompletionTransportOpen

@[expose] public noncomputable section
set_option autoImplicit false
universe u s i
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction

/-- Completion transport for finite words on the admissible short-word domain.
Source: the recursive completion comparison in
`fix-prop-coherence.proof.md`, step 5.  Induction on the word uses the
constructor equations supplied by the four strictly smaller transport lemmas;
input and unit cases are identities.
(blueprint: lem-sf-proper-open-lambda-completion-transport) -/
theorem properOpenLambdaCompletionTransport
    {D : FiniteFieldDatum.{u}} (Cf : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic Cf.l) E]
    [FiniteDimensional (Padic Cf.l) E] (o : Operations Cf.l E)
    {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S)
    {a : S} (B : Word W location a) (hB : B.length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource Cf.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hInputs : ∀ k : I, Admissible Cf.l E
      (IntegralSystemRealization.calculus Cf.l E (W (location k))) (K k)
      lo hi torLo torHi)
    (hBAdmissible : Word.admissible Cf.l E W location o K lo hi torLo torHi B) :
    (IntegralSystemRealization.calculus Cf.l E (W a)).reduction.map
        (B.completionMap Cf.l E W location o K) ≫
      B.r Cf.l E W location o K =
      properOpenOrdinaryR Cf.l E location o K B := by
  revert hB hBAdmissible
  induction B with
  | input k =>
    intro _ _
    simp [Word.completionMap, Word.r, properOpenOrdinaryR]
  | unit a =>
    intro _ _
    simp [Word.completionMap, Word.r, properOpenOrdinaryR]
  | @tensor a B C ihB ihC =>
    intro hBC hAd
    exact properOpenLambdaCompletionTransport_tensor Cf E o W location K lo hi torLo torHi
      hInputs B C hBC hAd
  | @pull a b f hs ht hq B ih =>
    intro hPull hAd
    exact properOpenLambdaCompletionTransport_pull Cf E o W location K lo hi torLo torHi
      hInputs f hs ht hq B hPull hAd
  | @push a b f hs ht hq hp B ih =>
    intro hPush hAd
    exact properOpenLambdaCompletionTransport_push Cf E o W location K lo hi torLo torHi
      hInputs f hs ht hq hp B hPush hAd
  | @«open» a b j hj hq B ih =>
    intro hOpen hAd
    exact properOpenLambdaCompletionTransport_open Cf E o W location K lo hi torLo torHi
      hInputs j hj hq B hOpen hAd

end WeilConjectures.OpenInterchangeReduction
