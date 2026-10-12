/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Sheaf.FieldTheory.SeparableExtension
import Sheaf.FieldTheory.FiniteInseparableElement
import Sheaf.FieldTheory.InseparableTensorNilpotent

/-!
# Reduced tensor products and separability of finite field extensions

Source: Stacks Project, Algebra, Lemma Tag 030W (implication (4) => (1)),
together with Lemma Tag 030V
(blueprint: lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- If the tensor product of a finite field extension with an algebraic closure is
reduced, then the extension is separable.
Source: Stacks Project, Algebra, Lemma Tag 030W (implication (4) => (1)),
together with Lemma Tag 030V.
(blueprint: lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable).
The proof is by contradiction: a nonseparable finite extension has an element
with inseparable minimal polynomial (the node
`lem-pc-finite-inseparable-element`), which yields a nonzero nilpotent in the
tensor product with an algebraic closure (the node
`lem-pc-inseparable-tensor-nilpotent`), contradicting reducedness.
-/
theorem finiteExtension_tensor_algebraicClosure_reduced_isSeparable
    (k : Type u) (K : Type v) (kbar : Type w)
    [Field k] [Field K] [Field kbar] [Algebra k K] [Algebra k kbar]
    [FiniteDimensional k K] [IsAlgClosure k kbar]
    [IsReduced (K ⊗[k] kbar)] :
    Algebra.IsSeparableExtension k K := by
  sorry

end Algebra
