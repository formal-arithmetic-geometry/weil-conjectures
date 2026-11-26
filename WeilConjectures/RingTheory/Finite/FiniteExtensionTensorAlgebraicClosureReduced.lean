/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.FieldTheory.Picard.FiniteInseparableElement
import WeilConjectures.FieldTheory.Picard.InseparableTensorNilpotent

/-!
# Reduced tensor products and separability of finite field extensions

If `K / k` is finite and `K ⊗[k] kbar` is reduced for an algebraic closure `kbar` of `k`, then
`K / k` is separable.

## Implementation details

The proof is by contradiction: a nonseparable finite extension has an element with inseparable
minimal polynomial, which yields a nonzero nilpotent in the tensor product with an algebraic
closure.

## References

* [Stacks, Tag 030W] (implication (4) ⇒ (1))
* [Stacks, Tag 030V]
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- If the tensor product of a finite field extension with an algebraic closure is
reduced, then the extension is separable. -/
theorem finiteExtension_tensor_algebraicClosure_reduced_isSeparable
    (k : Type u) (K : Type v) (kbar : Type w)
    [Field k] [Field K] [Field kbar] [Algebra k K] [Algebra k kbar]
    [FiniteDimensional k K] [IsAlgClosure k kbar]
    [IsReduced (K ⊗[k] kbar)] :
    Algebra.IsSeparableExtension k K := by
  classical
  by_contra hnot
  have hfinite : FieldExtension.degree k K ≠ ⊤ := by
    simp [FieldExtension.degree, show Module.Finite k K from inferInstance]
  obtain ⟨α, hα⟩ :=
    FieldExtension.exists_not_isSeparable_of_not_isSeparableExtension k K hfinite hnot
  exact (FieldTheory.inseparable_tensorProduct_algebraicClosure_not_isReduced
    k K kbar α hα).2 inferInstance

end Algebra
