/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTameSylow

/-!

# Tame extensions of a henselian discrete valuation ring and pro-`p` Galois groups

Let `R` be a henselian discrete valuation ring with separably closed residue field `k`,
fraction field `F` and uniformizer `π`. A finite separable extension `L` of `F` of degree `d`
invertible in `k` is totally ramified, so contains a `d`-th root `ρ` of `π`
(`IsDiscreteValuationRing.exists_pow_eq_algebraMap_of_dvd_finrank`); since `Xᵈ - π` is
irreducible over `F` (Eisenstein), `L = F(ρ)`.

Consequently (`IsDiscreteValuationRing.isPGroup_of_forall_pow_eq_mem`), if `p` is a prime such
that every natural number vanishing in `k` is divisible by `p`, `Ω` is an algebraic closure of
`F` and `L ⊆ Ω` is an intermediate field containing all roots `ρ` of `π` of order invertible
in `k`, then `Gal(M / L)` is a `p`-group for every finite Galois extension `M / L` in `Ω`: this is
the Sylow argument `IntermediateField.isPGroup_of_forall_mem`.

This generalises the `K⟦X⟧`-specific results of
`WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTameSylow`.

## Main statements

- `IsDiscreteValuationRing.irreducible_X_pow_sub_C_algebraMap`: `Xᵈ - π` is irreducible over `F`.
- `IsDiscreteValuationRing.exists_pow_eq_algebraMap_and_mem_adjoin`: a separable element `γ`
  of degree `d` invertible in `k` lies in `F(ρ)` for some `d`-th root `ρ` of `π`.
- `IsDiscreteValuationRing.isPGroup_of_forall_pow_eq_mem`: the pro-`p` statement.

-/

@[expose] public section

open Polynomial IntermediateField Module IsLocalRing

universe u

namespace IsDiscreteValuationRing

/-- **Eisenstein's criterion for `Xᵈ - π`**: for a uniformizer `π` of a discrete valuation ring
`R` and `d > 0`, the polynomial `Xᵈ - π` is irreducible over the fraction field of `R`. -/
theorem irreducible_X_pow_sub_C_algebraMap {R F : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] {π : R}
    (hπ : Irreducible π) {d : ℕ} (hd : 0 < d) :
    Irreducible ((Polynomial.X : F[X]) ^ d - Polynomial.C (algebraMap R F π)) := by
  have hmon := Polynomial.monic_X_pow_sub_C π hd.ne'
  have heis : ((Polynomial.X : R[X]) ^ d - Polynomial.C π).IsEisensteinAt
      (Ideal.span {π}) := by
    refine hmon.isEisensteinAt_of_mem_of_notMem ?_ ?_ ?_
    · exact (Ideal.span_singleton_eq_top).not.mpr hπ.not_isUnit
    · intro n hn
      rw [Polynomial.natDegree_X_pow_sub_C] at hn
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hn.ne, zero_sub]
      by_cases hn0 : n = 0
      · subst n
        simp [Polynomial.coeff_C]
      · simp [Polynomial.coeff_C, hn0]
    · simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hd.ne,
        Polynomial.coeff_C_zero, zero_sub, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
        dvd_neg]
      simpa only [pow_one] using
        (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).not.mpr (by omega : ¬ 2 ≤ 1)
  have hprime : (Ideal.span {π}).IsPrime :=
    (Ideal.span_singleton_prime hπ.ne_zero).mpr (irreducible_iff_prime.mp hπ)
  have hirr := heis.irreducible hprime hmon.isPrimitive
    (by simpa only [Polynomial.natDegree_X_pow_sub_C] using hd)
  have := (hmon.irreducible_iff_irreducible_map_fraction_map (K := F)).1 hirr
  simpa using this

variable {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field F] [Algebra R F]
  [IsFractionRing R F]

/-- **Tame elements over a henselian discrete valuation ring**: let `Ω` be an extension of the
fraction field `F` of `R` and `γ ∈ Ω` separable over `F` of degree `d` invertible in the
(separably closed) residue field of `R`. Then `γ ∈ F(ρ)` for a `d`-th root `ρ` of a given
uniformizer `π`. -/
theorem exists_pow_eq_algebraMap_and_mem_adjoin {Ω : Type u} [Field Ω] [Algebra F Ω]
    [Algebra R Ω] [IsScalarTower R F Ω] {π : R} (hπ : Irreducible π) {γ : Ω}
    (hγ : IsSeparable F γ) (hd : ((minpoly F γ).natDegree : ResidueField R) ≠ 0) :
    ∃ ρ : Ω, ρ ^ (minpoly F γ).natDegree = algebraMap R Ω π ∧ γ ∈ F⟮ρ⟯ := by
  set d := (minpoly F γ).natDegree
  have : Algebra.IsSeparable F F⟮γ⟯ := (isSeparable_adjoin_simple_iff_isSeparable F Ω).2 hγ
  have : FiniteDimensional F F⟮γ⟯ := adjoin.finiteDimensional hγ.isIntegral
  have hfin : finrank F F⟮γ⟯ = d := adjoin.finrank hγ.isIntegral
  obtain ⟨ρ, hρ⟩ := exists_pow_eq_algebraMap_of_dvd_finrank R F F⟮γ⟯ (N := d) hd
    (hfin ▸ dvd_rfl) hπ
  have hρ' : (ρ : Ω) ^ d = algebraMap R Ω π := by
    rw [← IntermediateField.coe_pow, hρ, IsScalarTower.algebraMap_apply R F F⟮γ⟯,
      IsScalarTower.algebraMap_apply R F Ω]
    rfl
  refine ⟨ρ, hρ', ?_⟩
  have hd0 : 0 < d := minpoly.natDegree_pos hγ.isIntegral
  have hle : F⟮(ρ : Ω)⟯ ≤ F⟮γ⟯ := adjoin_simple_le_iff.2 ρ.2
  have hroot : Polynomial.aeval (ρ : Ω)
      ((Polynomial.X : F[X]) ^ d - Polynomial.C (algebraMap R F π)) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      ← IsScalarTower.algebraMap_apply, hρ', sub_self]
  have hmin := minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_C_algebraMap hπ hd0)
    hroot (monic_X_pow_sub_C _ hd0.ne')
  have hρint : IsIntegral F (ρ : Ω) := (IsIntegral.of_finite F ρ).map F⟮γ⟯.val
  have heq : F⟮(ρ : Ω)⟯ = F⟮γ⟯ := by
    refine eq_of_le_of_finrank_eq hle ?_
    rw [adjoin.finrank hρint, ← hmin, natDegree_X_pow_sub_C, hfin]
  rw [heq]
  exact mem_adjoin_simple_self F γ

/-- **Pro-`p` Galois groups over a henselian trait**: let `R` be a henselian discrete valuation
ring with separably closed residue field `k` and fraction field `F`, `Ω` an algebraic closure of
`F`, `π` a uniformizer, `p` a prime such that every natural number vanishing in `k` is divisible
by `p`, and `L ⊆ Ω` an intermediate field containing every `n`-th root of `π` for `n` invertible
in `k`. Then every finite Galois extension `M` of `L` in `Ω` has a `p`-group as Galois group. -/
theorem isPGroup_of_forall_pow_eq_mem {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra R Ω]
    [IsScalarTower R F Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] {π : R} (hπ : Irreducible π)
    (L : IntermediateField F Ω) {p : ℕ} [Fact p.Prime]
    (hp : ∀ n : ℕ, (n : ResidueField R) = 0 → p ∣ n)
    (hL : ∀ (n : ℕ) (ρ : Ω), (n : ResidueField R) ≠ 0 → ρ ^ n = algebraMap R Ω π → ρ ∈ L)
    (M : IntermediateField L Ω) [FiniteDimensional L M] [IsGalois L M] :
    IsPGroup p Gal(M/L) := by
  refine IntermediateField.isPGroup_of_forall_mem _ (fun γ hγ hdeg ↦ ?_) M
  have hd : ((minpoly F γ).natDegree : ResidueField R) ≠ 0 := fun h ↦ hdeg (hp _ h)
  obtain ⟨ρ, hρ, hγρ⟩ := exists_pow_eq_algebraMap_and_mem_adjoin hπ hγ hd
  exact adjoin_simple_le_iff.2 (hL _ ρ hd hρ) hγρ

end IsDiscreteValuationRing
