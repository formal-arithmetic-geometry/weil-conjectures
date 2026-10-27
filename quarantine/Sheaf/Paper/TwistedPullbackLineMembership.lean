/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TwistedPullbackReductionData

/-! # Signed Tate tensor in the coefficient-calculus presentation

Source: blueprint integral-adjunction-bijection, Purity paragraph.
(blueprint: lem-sp-twisted-pullback-line-membership).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.SpTwistedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Tensor with the signed degree-zero Tate line in the fixed integral closed model
preserves the intrinsic integral constructible predicate.
Source: blueprint integral-adjunction-bijection, Purity paragraph;
Bhatt--Scholze 3.4.12, 3.5.1, 6.5.9; Stacks 07A4.
(blueprint: lem-sp-twisted-pullback-line-membership).

Proof: the completed first Tate line is locally free of rank one and has finite
locally constant reductions. Apply integral_line_reduction_restriction to it.
The PreservesIntegral clause gives membership after ordinary derived tensor
with every signed power. Identify that ordinary tensor presentation with the
integral closed tensor in the coefficient calculus: on simultaneous K-flat
representatives both are the same total sheaf tensor. Their universal derived
comparison and the single-complex localization isomorphism give a natural
isomorphism between these two presentations. Its second factor identifies the
generic signed power with integralTwistLine, including the dual at negative
integers and the coefficient unit at zero. Transport membership through this
isomorphism by sfIntegralConstructible_isClosedUnderIsomorphisms. This changes
no input and requires neither boundedness of the ambient complex nor a choice
of a finite-field datum. -/
theorem twistedPullbackLineMembership (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (m : ℤ)
    (M : sfIntegralConstructibleCategory l E X) :
    sfIntegralConstructible l E X
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.integralClosed.tensor.obj
        (M.obj, (DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E X m))) := by sorry

end WeilConjectures.SpTwistedPullback
