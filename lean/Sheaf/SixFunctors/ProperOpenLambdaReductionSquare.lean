/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module
public import Sheaf.SixFunctors.OpenInterchangeReductionData

/-! # The coefficient square for the four-factor proper/open restriction
Source: the open-adjunction and clopen expansion of the coherence proof.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction
/-- The coefficient square for the four-factor proper/open restriction.
Source: blueprint `fix-prop-coherence.proof.md`, open-adjunction/clopen expansion
(blueprint: lem-sf-proper-open-lambda-reduction-square).
Proof: Factor the open k through its clopen lift s into the fibre product of p and i.
The first factor in lambda is the right-adjoint conjugate of inverse cartesian
open base change. Expand that conjugate into the units and counits of the two
composite adjunctions; the cartesian open square and structural adjunction squares
then give its coefficient square. The restriction factor is restriction of the
inverse open compositor followed by inverse open unit. The open compositor is
itself the left-adjoint conjugate of the restriction compositor, so structural
squares and mate pasting give this second square. The clopen factor is the direct
image unit followed by direct image of inverse open unit; paste their structural
squares. Finally paste with the direct-image compositor and the equality of the
composite scheme map with r. This is precisely the specified four-factor lambda
on both the ringed and system sides. The six extra systems in generator
admissibility supply the internal common-window hypotheses. Cancel the endpoint
completion transports to obtain the stated completed square. -/
theorem properOpenLambdaReductionSquare
    {D : FiniteFieldDatum.{u}} (Cf : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic Cf.l) E]
    [FiniteDimensional (Padic Cf.l) E] (o : Operations Cf.l E)
    (hStructural : StructuralSquares.{u, s, i} Cf.l E D o)
    {S : Type s} (W : S → Scheme.{u}) (hW : FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S)
    {a b c d : S}
      (k : W a ⟶ W b) (r : W a ⟶ W c) (p : W b ⟶ W d) (i : W c ⟶ W d)
      (h : k ≫ p = r ≫ i) (hk : IsOpenImmersion k) (hki : QuasiCompact k)
      (hio : IsOpenImmersion i) (hii : QuasiCompact i)
      (hr : IsProper r) (hp : IsProper p) (B : Word W location a)
    (hSourceLength :
      (Word.pull i (by let := hio; infer_instance) (by let := hio; infer_instance) hii
          (Word.push p (by let := hp; infer_instance) (by let := hp; infer_instance)
            (by let := hp; infer_instance) hp (Word.open k hk hki B))).length ≤ 3)
    (hTargetLength : (Word.push r (by let := hr; infer_instance) (by let := hr; infer_instance)
          (by let := hr; infer_instance) hr B).length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource Cf.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hInputs : ∀ k : I, Admissible Cf.l E
      (IntegralSystemRealization.calculus Cf.l E (W (location k))) (K k)
      lo hi torLo torHi)
    (hSource : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.pull i (by let := hio; infer_instance) (by let := hio; infer_instance) hii
          (Word.push p (by let := hp; infer_instance) (by let := hp; infer_instance)
            (by let := hp; infer_instance) hp (Word.open k hk hki B))))
    (hTarget : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.push r (by let := hr; infer_instance) (by let := hr; infer_instance)
          (by let := hr; infer_instance) hr B))
    (hGenerator : GeneratorKind.admissible Cf.l E W location o K lo hi torLo torHi
      (GeneratorKind.properOpenLambda k r p i h hk hki hio hii hr hp B)) :
    Assertion Cf.l E W location o K
      (GeneratorKind.properOpenLambda k r p i h hk hki hio hii hr hp B) := by
  sorry
end WeilConjectures.OpenInterchangeReduction
