/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module
public import Sheaf.SixFunctors.OpenInterchangeReductionData

/-! # Unbounded proper/open lambda square
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
/-- The coefficient square for the open transpose of proper/open restriction.
Source: blueprint `fix-prop-coherence.proof.md`, open-adjunction/clopen expansion
(blueprint: lem-sf-proper-open-lambda-reduction-square-unbounded).
Proof: The four-factor lambda calculation pastes structural squares at every internal system.
The endpoint assumptions are the interchange endpoint bounds, with no additional bound
on the proper target restriction word.
The four-factor restriction argument gives the square for lambda and hence for
its inverse. Naturality of the canonical open reduction mate gives its open
whiskering. Paste with the assumed structural open-counit square. Expanding the
defining hom-equivalence shows that this composite is exactly Gamma in both
independent interpretations. The recursive ordinary-to-completed maps commute
with the composition by their naturality; cancel their invertible endpoint
components on the stated short-word domain. The internal length-four systems
are the six systems recorded by generator admissibility; no endpoint length
bound is applied to those internal systems. -/
theorem properOpenLambdaReductionSquare_unbounded
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
    (hSourceLength : (Word.open i hio hii (Word.push r (by let := hr; infer_instance)
          (by let := hr; infer_instance) (by let := hr; infer_instance) hr B)).length ≤ 3)
    (hTargetLength : (Word.push p (by let := hp; infer_instance) (by let := hp; infer_instance)
          (by let := hp; infer_instance) hp (Word.open k hk hki B)).length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource Cf.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hInputs : ∀ k : I, Admissible Cf.l E
      (IntegralSystemRealization.calculus Cf.l E (W (location k))) (K k)
      lo hi torLo torHi)
    (hSource : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.open i hio hii
      (Word.push r (by let := hr; infer_instance)
          (by let := hr; infer_instance) (by let := hr; infer_instance) hr B)))
    (hTarget : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.push p (by let := hp; infer_instance) (by let := hp; infer_instance)
          (by let := hp; infer_instance) hp (Word.open k hk hki B)))
    (hGenerator : GeneratorKind.admissible Cf.l E W location o K lo hi torLo torHi
      (GeneratorKind.properOpenInterchange k r p i h hk hki hio hii hr hp B)) :
    Assertion Cf.l E W location o K
      (GeneratorKind.properOpenLambda k r p i h hk hki hio hii hr hp B) := by
  sorry
end WeilConjectures.OpenInterchangeReduction
