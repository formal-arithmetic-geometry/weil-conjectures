/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.GroupTheory.TateModule

/-!
# Frobenius on roots of unity and the cyclotomic Tate module

Source: Deligne, Weil I (2.2), pp. 280--281, and Weil II (1.1.7), pp. 150--151
(blueprint: lem-pur-frobenius-roots-of-unity-power).

The integral cyclotomic Tate module is `AddCommGroup.tateModule ℓ (Additive D.kˣ)`, the
unfolding of the existing upstream `cyclotomicTateModule D.k ℓ`. Its coordinates
are units killed by the powers of the coefficient prime, written additively, and its
transition maps are multiplication by that prime. The induced maps below are the existing
coordinatewise linear maps `AddCommGroup.tateModule.map`. A linear equivalence with the
coefficient ring expresses freeness of rank one. The unit `u` is specified by its value `q`,
so the scalar actions are independent of any choice of generator.
-/

@[expose] public section

universe u

namespace WeilConjectures.FiniteFieldDatum

/-- Arithmetic Frobenius raises roots of unity to the `q`-th power; geometric Frobenius
raises them to any inverse exponent modulo their order. On the integral cyclotomic Tate
module these are multiplication by the unit `q` and its inverse.

Source: Deligne, Weil I (2.2), pp. 280--281, and Weil II (1.1.7), pp. 150--151
(blueprint: lem-pur-frobenius-roots-of-unity-power).

Proof: Since `N` is prime to the characteristic, `X ^ N - 1` is separable and splits over
`D.k`. It has exactly `N` roots, and the finite subgroup of units consisting of those roots
is cyclic. Any field automorphism preserves the equation and its inverse does too, giving
bijectivity on the roots. Arithmetic Frobenius is `z ↦ z ^ q`. Since `q = p ^ a` is coprime
to `N`, Bezout gives an integer inverse `q'` modulo `N`. On an `N`-th root, raising to `q'`
is inverse to raising to `q`; this also works for negative `q'` because roots are units.
For the coefficient prime `ℓ ≠ p`, choose a primitive `ℓ`-th root and successively lift it
along the surjective `ℓ`-power maps. These lifts are primitive of orders `ℓ ^ r` and form a
compatible generator of the inverse limit. Expressing every compatible system in these
cyclic generators identifies its exponents with `ℤ_[ℓ]`, proving freeness of rank one.
The coordinatewise arithmetic action raises each coordinate to `q`, hence is scalar `q`
under the canonical `ℤ_[ℓ]`-action. This scalar is a unit because `ℓ` does not divide `q`.
The coordinatewise geometric action is its inverse, hence is scalar `q⁻¹`.
The imported upstream definitions of the Tate module and its induced maps supply exactly
these compatible systems and their componentwise actions; no generator is chosen in the
statement. -/
theorem frobenius_rootsOfUnity_power (D : WeilConjectures.FiniteFieldDatum.{u})
    (N : ℕ) (hN : 1 ≤ N) (hNp : N.Coprime D.p) :
    (IsCyclic (rootsOfUnity N D.k) ∧ Nat.card (rootsOfUnity N D.k) = N ∧
      ∀ σ : D.k ≃+* D.k,
        Set.BijOn (Units.map σ.toRingHom.toMonoidHom)
          (rootsOfUnity N D.k) (rootsOfUnity N D.k)) ∧
    ((∀ ζ : rootsOfUnity N D.k,
        (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
          D.k _ _ _) ((ζ : D.kˣ) : D.k) = ((ζ : D.kˣ) : D.k) ^ D.q) ∧
      (∃ q' : ℤ, Int.ModEq (N : ℤ) ((D.q : ℤ) * q') 1) ∧
      ∀ q' : ℤ, Int.ModEq (N : ℤ) ((D.q : ℤ) * q') 1 →
        ∀ ζ : rootsOfUnity N D.k,
          Units.map
            (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
              D.k _ _ _).symm.toRingHom.toMonoidHom (ζ : D.kˣ) = (ζ : D.kˣ) ^ q') ∧
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ D.p →
      Nonempty (AddCommGroup.tateModule ℓ (Additive D.kˣ) ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ]) ∧
        ∃ u : ℤ_[ℓ]ˣ, (u : ℤ_[ℓ]) = (D.q : ℤ_[ℓ]) ∧
          ∀ t : AddCommGroup.tateModule ℓ (Additive D.kˣ),
            AddCommGroup.tateModule.map
              (Units.map
                (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
                  D.k _ _ _).toRingHom.toMonoidHom).toAdditive t = (u : ℤ_[ℓ]) • t ∧
            AddCommGroup.tateModule.map
              (Units.map
                (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
                  D.k _ _ _).symm.toRingHom.toMonoidHom).toAdditive t =
              (↑(u⁻¹) : ℤ_[ℓ]) • t) :=
  sorry

end WeilConjectures.FiniteFieldDatum
