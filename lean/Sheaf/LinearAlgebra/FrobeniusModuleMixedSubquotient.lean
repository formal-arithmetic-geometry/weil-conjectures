/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact

/-!
# Mixed weight bounds on Frobenius-stable subquotients

Source: Weil-conjectures blueprint, chapter `sec-deligne-laumon-a1`, unit
`sk-l-dl-a1-endpoints`, node `lem-a1-subquotient-extension-bounds`
(blueprint: lem-a1-subquotient-extension-bounds).

The subquotient is `S ⧸ U`, where `S` is a stable subspace of the ambient module
and `U` is a stable subspace of `S`. Its Frobenius is the canonical restriction
followed by the canonical quotient automorphism from Mathlib.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u v

namespace FrobeniusModule

/-- Every Frobenius-stable subquotient of a module mixed of weights at most `w`
is mixed of weights at most `w`, with the same prime power and coefficient isomorphism.

Source: Weil-conjectures blueprint, chapter `sec-deligne-laumon-a1`, unit
`sk-l-dl-a1-endpoints`, node `lem-a1-subquotient-extension-bounds`
(blueprint: lem-a1-subquotient-extension-bounds).

Proof plan: first choose the finite stable filtration supplied by
`def-weil-frobenius-module-weights`. Iterate the characteristic-polynomial
factorization of `p-linear-filtration` over that filtration. Each ambient eigenvalue
then belongs to a pure graded piece of weight at most `w`, so its iota-modulus is
at most `(p ^ a) ^ (w / 2)`. The zero module has an empty filtration and no eigenvalues.
Next apply the same factorization to the stable subspace `S` and then to `U` in `S`.
The characteristic polynomial on `S ⧸ U` divides the ambient one, so every eigenvalue
on the subquotient obeys the same bound. Finite dimension and invertibility make the
restricted and quotient Frobenius automorphisms. Finally apply the filtered criterion
of `lem-a1-punctual-bound-module-mixed`: an invariant composition filtration over the
algebraically closed coefficient field has one-dimensional nonzero factors, whose
actual weights are at most `w`. This gives the required mixed filtration without any
semisimplicity or stable-complement assumption, including `U = S` and zero modules. -/
theorem IsMixedOfWeightsAtMost.subquotient
    (p a ell : ℕ) [Fact (Nat.Prime p)] (ha : 1 ≤ a)
    [Fact (Nat.Prime ell)] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra (ℚ_[ell]) Qlb] (hQ : IsAlgClosure (ℚ_[ell]) Qlb)
    (iota : Qlb ≃+* ℂ) (M : FrobeniusModule.{u, v} Qlb) (w : ℝ)
    (hM : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota M w)
    (S : Submodule Qlb M.carrier) (hS : S.map M.frobenius.toLinearMap = S)
    (U : Submodule Qlb S)
    (hU : U.map (M.frobenius.ofSubmodules S S hS).toLinearMap = U) :
    IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota
      { carrier := S ⧸ U
        frobenius := Submodule.Quotient.equiv U U (M.frobenius.ofSubmodules S S hS) hU } w := by
  sorry

end FrobeniusModule
