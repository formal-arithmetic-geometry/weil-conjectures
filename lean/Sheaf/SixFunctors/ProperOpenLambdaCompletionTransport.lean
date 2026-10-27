/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y9
-/
module

public import Sheaf.SixFunctors.ProperOpenLambdaOrdinarySquare

@[expose] public noncomputable section
set_option autoImplicit false
universe u s i
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Completion transport for finite words on the admissible short-word domain.
Source: the recursive completion comparison in
`fix-prop-coherence.proof.md`, step 5.  Induction on the word uses the
normalized tensor, pull, push and open comparison formulas; admissibility gives
the common support and torsion bounds needed by those formulas.  The statement
is deliberately independent of any generator square.
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
  sorry


end WeilConjectures.OpenInterchangeReduction
