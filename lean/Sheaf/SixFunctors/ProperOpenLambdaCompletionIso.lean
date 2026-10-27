/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y9
-/
module

public import Sheaf.SixFunctors.GeneratorReductionData
import Sheaf.SixFunctors.ShortWordCompletionIsomorphism

@[expose] public noncomputable section
set_option autoImplicit false
universe u s i
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Endpoint completion maps are isomorphisms on the short admissible domain.
Source: the short-word completion effectivity argument in
`fix-prop-coherence.proof.md`, step 5.  Induction on the word reduces tensor,
pull, push and open cases to the primitive completion effectivity maps; the
admissibility hypothesis supplies the required normalized systems.
(blueprint: lem-sf-proper-open-lambda-completion-isiso) -/
theorem properOpenLambdaCompletionIso
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
    IsIso (B.completionMap Cf.l E W location o K) := by
  exact GeneratorReduction.completionMap_isIso Cf.l E W location o B hB K lo hi torLo torHi
    hInputs hBAdmissible

end WeilConjectures.OpenInterchangeReduction
