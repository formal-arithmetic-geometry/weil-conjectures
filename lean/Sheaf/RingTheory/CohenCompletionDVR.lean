/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.Flat

/-!
# The completion of a flat local extension of the p-adic integers is a DVR

Source: Stacks Project, Algebra, proof of Lemma Tag 0328 and the factorization
argument in Lemma Tag 00PD.
(blueprint: lem-weil-pbc-cohen-completion-dvr).
-/

@[expose] public section

universe u

/-- The fixed maximal-ideal completion of a flat local extension of the p-adic
integers with maximal ideal `(p)` is a domain and a discrete valuation ring.
Source: Stacks Project, Algebra, proof of Lemma Tag 0328; the final factorization
argument is the last assertion of Lemma Tag 00PD.
(blueprint: lem-weil-pbc-cohen-completion-dvr)

Proof:
1. Flatness over the domain `ℤ_[p]` makes multiplication by `p` injective on `S`:
   tensor the injective multiplication map on `ℤ_[p]` with `S`. Write `A` for the
   explicit completion `AdicCompletion (maximalIdeal S) S`.
2. The maximal ideal of `S` is the principal ideal `(p)`, hence finitely generated.
   The completion results of Tag 05GG make `A` complete and local, with maximal
   ideal `(p)` and nonzero field quotient `S/(p)`.
3. Multiplication by `p` is injective on `A` directly. If `p*x = 0`, choose a lift
   `y` of the component of `x` in `S/(p^(n+1))`. Then `p*y = p^(n+1)*z` for some
   `z` in `S`. Cancel `p` using step 1 to get `y = p^n*z`. Thus the component of
   `x` in `S/(p^n)` is zero for every `n`; componentwise equality gives `x = 0`.
4. Separatedness says that an element in every `(p)^n` is zero. For nonzero `x`,
   the set of `n` for which `x` belongs to `(p)^n` is a nonempty bounded initial
   segment of the natural numbers: choose a power not containing `x`, and use
   the decreasing filtration. Take its largest member `n` and write `x = p^n*u`.
   If `u` were a nonunit, locality would put it in `(p)`, contradicting maximality.
5. Products of two nonzero elements are `p^(n+m)` times a unit. They are nonzero
   by step 3 and nontriviality of `A`; hence `A` is a domain. The element `p` is
   nonzero by step 3 and is a nonunit since it is in the maximal ideal. Its
   principal ideal is maximal, so `p` is prime, hence irreducible in the domain.
6. Every nonzero ideal contains an element of least exponent in step 4. This
   element generates the ideal because all other elements are divisible by its
   power of `p`, and its unit factor is invertible. Thus every ideal is principal.
   The nonzero nonunit `p` shows that `A` is not a field. Together with locality
   and the domain property this is precisely a discrete valuation ring. -/
theorem adicCompletion_dvr_of_flat_padicInt (p : ℕ) [Fact p.Prime]
    (S : Type u) [CommRing S] [IsLocalRing S] (φ : ℤ_[p] →+* S)
    (hFlat : φ.Flat) (hMax : IsLocalRing.maximalIdeal S = Ideal.span {(p : S)}) :
    ∃ (_ : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal S) S)),
      IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
  sorry
