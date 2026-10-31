/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import WeilConjectures.RingTheory.UniversalInjectiveFiniteTest
import WeilConjectures.SecTraceFormula.UniversallyExactFpSplit

/-!
# Finite tensor-kernel tests detect factorization

Source: Stacks Project, Algebra, Tags 059C and 059D (`lemma-domination-fp`
and `lemma-domination`).

The statement records that, when the cokernel of a linear map is finitely
presented, inclusion of the kernels after tensoring with every finitely
presented module forces the second map to factor through the first.
(blueprint: lem-trf-tensor-kernel-factorization)
-/

@[expose] public section
set_option autoImplicit false

universe uR uU uV uW uQ

namespace WeilConjectures

/-- Finite tensor-kernel tests detect factorization when the cokernel is finitely presented.

This is the statement of Stacks Project, Algebra, Tags 059C and 059D
(`lemma-domination-fp` and `lemma-domination`).  The quotient is represented
by `V ⧸ LinearMap.range f`, and tensoring on the right uses Mathlib's
`LinearMap.rTensor`.  The proof is postponed: the pushout construction and
universal-injectivity argument are the proof described in the source.
(blueprint: lem-trf-tensor-kernel-factorization) -/
theorem tensorKernelFactorization
    (R : Type uR) [CommRing R]
    (U : Type uU) [AddCommGroup U] [Module R U]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (W : Type uW) [AddCommGroup W] [Module R W]
    (f : U →ₗ[R] V) (g : U →ₗ[R] W)
    [Module.FinitePresentation R (V ⧸ LinearMap.range f)]
    (hker : ∀ (Q : Type uQ) [AddCommGroup Q] [Module R Q]
      [Module.FinitePresentation R Q],
      LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q)) :
    ∃ h : V →ₗ[R] W, g = h.comp f := by
  sorry

end WeilConjectures
