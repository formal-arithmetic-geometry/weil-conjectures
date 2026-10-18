/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF Q44
-/
module

public import Sheaf.LinearAlgebra.FrobeniusModuleWeights

/-!
# Spectrum of an exact Frobenius sequence

Source: the blueprint of the Weil conjectures, chapter `sec-deligne-laumon-a1`, unit
`sk-l-dl-a1-endpoints`, node `lem-a1-spectrum-exact-sequence`, order 2732
(blueprint: lem-a1-spectrum-exact-sequence).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u' u u'' v

namespace FrobeniusModule

/--
For a short exact sequence of finite Frobenius modules whose maps commute with Frobenius, the
multiset of complex Frobenius eigenvalues, with algebraic multiplicity, is the multiset union of
the corresponding multisets for the submodule and quotient.  The spectrum of a module is rendered
by mapping the roots of its Frobenius characteristic polynomial along the fixed coefficient
isomorphism.

Source: the blueprint of the Weil conjectures, chapter `sec-deligne-laumon-a1`, unit
`sk-l-dl-a1-endpoints`, node `lem-a1-spectrum-exact-sequence`, order 2732
(blueprint: lem-a1-spectrum-exact-sequence).  The proof writes an adapted basis for the exact
sequence, obtains a block upper-triangular Frobenius matrix, applies the determinant product for
the invariant filtration, and factors roots of the resulting characteristic-polynomial product;
root multiplicities therefore add, including the zero-dimensional cases.
-/
theorem spectrum_exact_sequence
    (p a ell : ℕ) [Fact (Nat.Prime p)] (_ha : 1 ≤ a)
    [Fact (Nat.Prime ell)] (_hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra (ℚ_[ell]) Qlb] (_hQ : IsAlgClosure (ℚ_[ell]) Qlb)
    (iota : Qlb ≃+* ℂ)
    (V' : FrobeniusModule.{u', v} Qlb) (V : FrobeniusModule.{u, v} Qlb)
    (V'' : FrobeniusModule.{u'', v} Qlb)
    (ι : V'.carrier →ₗ[Qlb] V.carrier) (π : V.carrier →ₗ[Qlb] V''.carrier)
    (hι : Function.Injective ι) (h_exact : Function.Exact ι π)
    (hπ : Function.Surjective π)
    (hιF : ∀ x : V'.carrier, ι (V'.frobenius x) = V.frobenius (ι x))
    (hπF : ∀ x : V.carrier, π (V.frobenius x) = V''.frobenius (π x)) :
    Multiset.map iota V.frobeniusEnd.charpoly.roots =
      Multiset.map iota V'.frobeniusEnd.charpoly.roots +
        Multiset.map iota V''.frobeniusEnd.charpoly.roots := by
  sorry

end FrobeniusModule
