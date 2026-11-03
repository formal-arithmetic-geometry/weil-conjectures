/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData

/-! # Proper/open interchange from the lambda square
Source: the open-adjunction and clopen expansion of the coherence proof.
(blueprint: lem-sf-proper-open-interchange-from-lambda)
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

/--
The proper/open interchange square is obtained by transposing the inverse lambda
square under the open adjunction and pasting the open counit square.  The displayed
lambda square is the strictly smaller input: the transpose calculation uses only
adjunction naturality, the two triangle identities, and the structural open-counit
square.  The calculation is performed on the specified whole-system maps, so no
faithfulness of evaluation is used.
Source: blueprint `fix-prop-coherence.proof.md`, final Gamma step.
(blueprint: lem-sf-proper-open-interchange-from-lambda)
-/
theorem properOpenInterchange_from_lambda_square
    {D : FiniteFieldDatum.{u}} (Cf : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic Cf.l) E]
    [FiniteDimensional (Padic Cf.l) E] (o : Operations Cf.l E)
    (hStructural : StructuralSquares.{u, s, i} Cf.l E D o)
    {S : Type s} (W : S → Scheme.{u}) (hW : FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S)
    {a b c d : S}
      (k : W a ⟶ W b) (r : W a ⟶ W c) (p : W b ⟶ W d) (j : W c ⟶ W d)
      (h : k ≫ p = r ≫ j) (hk : IsOpenImmersion k) (hki : QuasiCompact k)
      (hjo : IsOpenImmersion j) (hji : QuasiCompact j)
      (hr : IsProper r) (hp : IsProper p) (B : Word W location a)
    (hSourceLength : (Word.open j hjo hji (Word.push r (by let := hr; infer_instance)
          (by let := hr; infer_instance) (by let := hr; infer_instance) hr B)).length ≤ 3)
    (hTargetLength : (Word.push p (by let := hp; infer_instance) (by let := hp; infer_instance)
          (by let := hp; infer_instance) hp (Word.open k hk hki B)).length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource Cf.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hInputs : ∀ k : I, Admissible Cf.l E
      (IntegralSystemRealization.calculus Cf.l E (W (location k))) (K k)
      lo hi torLo torHi)
    (hSource : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.open j hjo hji
      (Word.push r (by let := hr; infer_instance)
          (by let := hr; infer_instance) (by let := hr; infer_instance) hr B)))
    (hTarget : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.push p (by let := hp; infer_instance) (by let := hp; infer_instance)
          (by let := hp; infer_instance) hp (Word.open k hk hki B)))
    (hGenerator : GeneratorKind.admissible Cf.l E W location o K lo hi torLo torHi
      (GeneratorKind.properOpenInterchange k r p j h hk hki hjo hji hr hp B))
    (hLambda : Assertion Cf.l E W location o K
      (GeneratorKind.properOpenLambda k r p j h hk hki hjo hji hr hp B)) :
    Assertion Cf.l E W location o K
      (GeneratorKind.properOpenInterchange k r p j h hk hki hjo hji hr hp B) := by
  sorry

end WeilConjectures.OpenInterchangeReduction
