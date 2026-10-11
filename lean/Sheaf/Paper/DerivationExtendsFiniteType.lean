import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.FiniteType

/-!
# Derivations after finite type localization extensions

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 07PE, final statement
(blueprint: lem-weil-pbc-derivation-extends-finite-type-extension).
-/

universe u v

namespace RingTheory

/--
(blueprint: lem-weil-pbc-derivation-extends-finite-type-extension)
Stacks Project, More on Algebra, Lemma 07PE, final statement. Let `R ⊆ R'` be a finite
type extension of commutative rings and let `g : R` be a nonzerodivisor in `R'` such that
the canonical map `R_g → R'_g` is bijective. Then for every derivation `D` of `R` there are
`N` and a derivation `D'` of `R'` with `D' r = g ^ N * D r` for `r ∈ R`. Absolute
derivations are represented as derivations over `ℤ`, as in
`Derivation.exists_completion_and_unique_localization`.

Proof, following the node's steps:
1. Choose generators `x₁, …, xₘ` of `R'` over `R`; the maps `R → R_g`, `R' → R'_g` are
   injective (`g` is a nonzerodivisor in `R'` and `R ⊆ R'`), and the bijective map
   `φ : R_g → R'_g` is a ring isomorphism compatible with `R ⊆ R'`.
2. By `Derivation.exists_completion_and_unique_localization` (2), `D` extends to a derivation
   `D_g` of `R_g`; transporting along `φ` gives a derivation `δ` of `R'_g` extending `D`.
3. By surjectivity of `φ` and since `g` is a nonzerodivisor, `g ^ nᵢ * xᵢ ∈ R`; take
   `N = max nᵢ` and `aᵢ = g ^ N * xᵢ ∈ R`.
4. By the Leibniz rule, `g ^ (N+1) δ(xᵢ) = -N g ^ N xᵢ D(g) + g D(aᵢ)` comes from `R'`.
5. The elements `t ∈ R'` with `g ^ (N+1) δ(t) ∈ R'` form a subring containing `R` and the
   `xᵢ` (Leibniz rule), hence all of `R'`.
6. Restricting `g ^ (N+1) δ` to `R'` gives the derivation `D'` with `D' r = g ^ (N+1) D r`.
-/
theorem derivation_extends_finite_type_extension
    (R : Type u) (R' : Type v) [CommRing R] [CommRing R'] [Algebra R R']
    (hfinite : Algebra.FiniteType R R')
    (hinj : Function.Injective (algebraMap R R'))
    (g : R) (hreg : algebraMap R R' g ∈ nonZeroDivisors R')
    (hiso : Function.Bijective
      (IsLocalization.Away.map (Localization.Away g)
        (Localization.Away (algebraMap R R' g)) (algebraMap R R') g))
    (D : Derivation ℤ R R) :
    ∃ N : ℕ, ∃ D' : Derivation ℤ R' R',
      ∀ r : R, D' (algebraMap R R' r) = algebraMap R R' (g ^ N * D r) := by
  sorry

end RingTheory
