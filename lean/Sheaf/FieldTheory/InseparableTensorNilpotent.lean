import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Inseparable elements and nilpotents after algebraic-closure base change

Source: Stacks Project, Algebra, Lemma Tags 030V and 030W
(blueprint: lem-pc-inseparable-tensor-nilpotent).
-/

open scoped TensorProduct

namespace FieldTheory

/-- An element of a finite extension `K/k` with inseparable minimal polynomial produces a
nonzero nilpotent in `K ⊗[k] kbar` for an algebraic closure `kbar` of `k`, so this tensor
product is not reduced.

Source: Stacks Project, Algebra, Lemma Tags 030V and 030W
(blueprint: lem-pc-inseparable-tensor-nilpotent).
The proof has four steps. First, the inseparable minimal polynomial `P` of `α`
has a repeated root `β` in `kbar`, so `P = (T - β)^2 Q` over `kbar`.
Second, the quotient isomorphism of
`lem-weil-pbc-minimal-polynomial-quotient-field-iso` identifies
`k(α) ⊗[k] kbar` with `kbar[T]/(P)`. The class of
`g = (T - β) Q` is nonzero since its degree is less than that of `P`, and
its square vanishes since `g^2 = P Q`.
Third, the inclusion `k(α) → K` remains injective after tensoring over the
field `k`, so this nilpotent remains nonzero in `K ⊗[k] kbar`.
Fourth, a ring with a nonzero nilpotent is not reduced.
-/
theorem inseparable_tensorProduct_algebraicClosure_not_isReduced
    (k K kbar : Type*) [Field k] [Field K] [Field kbar] [Algebra k K] [Algebra k kbar]
    [FiniteDimensional k K] [IsAlgClosure k kbar]
    (α : K) (hαinseparable : ¬ IsSeparable k α) :
    (∃ x : K ⊗[k] kbar, x ≠ 0 ∧ IsNilpotent x) ∧ ¬ IsReduced (K ⊗[k] kbar) := by
  sorry

end FieldTheory
