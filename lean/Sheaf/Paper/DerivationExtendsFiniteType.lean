module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FiniteType
import Sheaf.Paper.DerivationAwayTransport
import Sheaf.Paper.DerivationAwayFiniteTypeCore

/-!
# Derivations after finite type localization extensions

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 07PE, final statement
(blueprint: lem-weil-pbc-derivation-extends-finite-type-extension).
-/

@[expose] public section

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

Proof:
1. By `exists_derivation_away_transport`, extend `D` to `R_g` using
   `Derivation.exists_completion_and_unique_localization`, then conjugate along the
   bijective localization map to obtain a derivation `δ` on `R'_g` extending `D`.
2. By `exists_derivation_of_finiteType_away_extension`, clear the denominators of the
   values of `δ` on finitely many algebra generators of `R'`. A common power of `g`
   makes those values integral. Additivity and the Leibniz rule show that the scaled
   derivation preserves all of `R'`, including the coefficients from `R`.
3. The map `R' → R'_g` is injective since `g` is regular. Restrict the scaled derivation
   using unique preimages to obtain `D'` and its asserted values on `R`.
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
  obtain ⟨δ, hδ⟩ := exists_derivation_away_transport R R' hinj g hiso D
  exact exists_derivation_of_finiteType_away_extension R R' hfinite hinj g hreg D δ hδ

end RingTheory
