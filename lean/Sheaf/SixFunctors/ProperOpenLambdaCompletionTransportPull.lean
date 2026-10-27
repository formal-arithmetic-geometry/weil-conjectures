/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.SixFunctors.ProperOpenLambdaOrdinarySquare

@[expose] public noncomputable section
set_option autoImplicit false
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
  sorry

end WeilConjectures.OpenInterchangeReduction
