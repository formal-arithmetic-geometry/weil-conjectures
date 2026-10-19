/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF Q44
-/
module

public import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic

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
(blueprint: lem-a1-spectrum-exact-sequence). The proof identifies the submodule with the kernel
of the quotient map and the quotient by this kernel with the final module. These equivariant
linear equivalences identify their characteristic polynomials with the two factors supplied by
`LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`. Taking roots of the product and
mapping along `iota` gives the result, including the zero-dimensional cases.
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
  classical
  have hker : LinearMap.ker π = LinearMap.range ι := LinearMap.exact_iff.mp h_exact
  have hstable : LinearMap.ker π ≤ (LinearMap.ker π).comap V.frobeniusEnd := by
    intro x hx
    change π (V.frobenius x) = 0
    rw [hπF, show π x = 0 from hx, map_zero]
  let eι : V'.carrier ≃ₗ[Qlb] LinearMap.ker π :=
    (LinearEquiv.ofInjective ι hι).trans
      (LinearEquiv.ofEq (LinearMap.range ι) (LinearMap.ker π) hker.symm)
  have hsub : V'.frobeniusEnd.charpoly = (V.frobeniusEnd.restrict hstable).charpoly := by
    apply LinearMap.charpoly_eq_of_comp_eq eι
    ext x
    exact hιF x
  let eπ := π.quotKerEquivOfSurjective hπ
  have hquot : ((LinearMap.ker π).mapQ (LinearMap.ker π) V.frobeniusEnd hstable).charpoly =
      V''.frobeniusEnd.charpoly := by
    apply LinearMap.charpoly_eq_of_comp_eq eπ
    ext x
    change π (V.frobenius x) = V''.frobenius (π x)
    exact hπF x
  have hchar : V.frobeniusEnd.charpoly =
      V'.frobeniusEnd.charpoly * V''.frobeniusEnd.charpoly := by
    rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ
      V.frobeniusEnd (LinearMap.ker π) hstable, ← hsub, hquot]
  rw [hchar, Polynomial.roots_mul
    (mul_ne_zero V'.frobeniusEnd.charpoly_monic.ne_zero
      V''.frobeniusEnd.charpoly_monic.ne_zero), Multiset.map_add]

end FrobeniusModule
