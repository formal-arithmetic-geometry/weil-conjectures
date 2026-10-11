/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.Basic

/-!
# Exactness of the Cech sequence for a module localization cover

Source: Stacks Project, Algebra, Lemma 00EK (label `lemma-cover-module`)
(blueprint: lem-weil-pbc-cover-module-exact).
-/

universe u v

namespace RingTheory

/-- Powers of a divisor of `h` act invertibly on `M_h`. This is the invertibility
needed in the notation step of Stacks Project, Algebra, Lemma 00EK, using the universal
property in Lemma 07K0 (blueprint: lem-weil-pbc-cover-module-exact).

Proof: write `h = a * b`. Multiplication by `h` is a unit endomorphism of `M_h`, by
`IsLocalizedModule.map_units`. The commuting endomorphisms given by `a` and `b` therefore
are units individually. Every element of `Submonoid.powers a` is a power of `a`, so its
endomorphism is a unit as well. No map or localization is defined anew here. -/
theorem localizationAway_map_units_of_dvd {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (a h : R) (ha : a ∣ h) :
    ∀ x : Submonoid.powers a,
      IsUnit (algebraMap R (Module.End R (LocalizedModule.Away h M)) (x : R)) := by
  sorry

/-- The Cech equalizer statement for a finite principal-open cover of a module.
Source: Stacks Project, Algebra, Lemma 00EK (label `lemma-cover-module`)
(blueprint: lem-weil-pbc-cover-module-exact).

The local abbreviation `ρ` is Mathlib's `IsLocalizedModule.lift` of the localization map
`m ↦ m/1`; Lemma 07K0 characterizes it uniquely by sending `m/1` to `m/1`. For `h = a*b`,
it sends `m/a^e` to `b^e*m/(a*b)^e`. Finite products are the finite direct sums in the source.

Proof (the node's direct partition-of-unity proof, rather than the source's reduction
at maximal ideals):
1. The two canonical lifts send `m/1` to `m/1`, so `β α = 0`. Fraction representations,
   equality after multiplying by a power, and cancellation use
   `def-weil-pbc-module-localization-away`.
2. If every localization of `m` vanishes, `lem-weil-pbc-localized-span-eq-zero` gives
   `m = 0`. Equivalently choose a common annihilating exponent and express 1 as a linear
   combination of the powers using `lem-weil-pbc-span-pow-eq-top`.
3. Write the compatible sections as `s_i = x_i/f_i^e_i`; choose a common exponent `N`
   and replace each numerator by `m_i = f_i^(N-e_i)*x_i`.
4. Equality on each overlap gives an exponent `k_ij` annihilating
   `f_j^N*m_i - f_i^N*m_j` after multiplication by `(f_i*f_j)^k_ij`. A common exponent
   `K` gives `f_i^K*f_j^(N+K)*m_i = f_i^(N+K)*f_j^K*m_j` for every pair.
5. By `lem-weil-pbc-span-pow-eq-top`, choose coefficients `a_i` with
   `sum a_i*f_i^(N+K) = 1`. Set `m = sum a_i*f_i^K*m_i`. Step 4 gives
   `f_j^(N+K)*m = f_j^K*m_j`, so in `M_(f_j)` one has `m/1 = m_j/f_j^N = s_j`.
6. Two glued elements have difference zero in every localization, hence are equal by
   step 2. If the cover is empty, its span hypothesis forces the zero ring and therefore
   the zero module; both clauses still hold without taking a maximum of an empty set. -/
theorem coverModuleExact {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
    [Module R M] (n : ℕ) (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = ⊤) :
    let ρ := fun (a h : R) (ha : a ∣ h) =>
      IsLocalizedModule.lift (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
        (localizationAway_map_units_of_dvd (M := M) a h ha)
    (∀ m : M, (∀ i : Fin n,
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m = 0) → m = 0) ∧
    (∀ (s : ∀ i : Fin n, LocalizedModule.Away (f i) M),
      (∀ i j : Fin n,
        ρ (f i) (f i * f j) (dvd_mul_right (f i) (f j)) (s i) =
          ρ (f j) (f i * f j) (dvd_mul_left (f j) (f i)) (s j)) →
      ∃! m : M, ∀ i : Fin n,
        LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m = s i) := by
  sorry

end RingTheory
