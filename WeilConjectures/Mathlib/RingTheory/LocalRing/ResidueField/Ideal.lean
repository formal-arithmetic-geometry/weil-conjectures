/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# Lifting minimal polynomials over residue fields

## Main statements

- `Ideal.ResidueField.exists_monic_map_eq_minpoly`: for a prime `𝔭` of `R` and an element `α`
  integral over `κ(𝔭)`, some multiple `c • α` with `c ∉ 𝔭` has a minimal polynomial over `κ(𝔭)`
  which lifts to a monic polynomial over `R`.
-/

@[expose] public section

open Polynomial

namespace Ideal.ResidueField

variable {R : Type*} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]

/-- Every element of `κ(𝔭)` becomes the image of an element of `R` after multiplication by the
image of a suitable `c ∉ 𝔭`. -/
theorem exists_notMem_mul_mem_range (x : 𝔭.ResidueField) :
    ∃ c ∉ 𝔭, algebraMap R 𝔭.ResidueField c * x ∈ Set.range (algebraMap R 𝔭.ResidueField) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ 𝔭) x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb' : b ∉ 𝔭 := fun h ↦ nonZeroDivisors.ne_zero hb (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  refine ⟨b, hb', a, ?_⟩
  have h0 : algebraMap R 𝔭.ResidueField b ≠ 0 := by
    rwa [Ne, Ideal.algebraMap_residueField_eq_zero]
  simp only [IsScalarTower.algebraMap_apply R (R ⧸ 𝔭) 𝔭.ResidueField,
    Ideal.Quotient.algebraMap_eq] at h0 ⊢
  rw [mul_div_cancel₀ _ h0]

/-- Let `𝔭` be a prime of a commutative ring `R` and `α` an element of a field extension `L` of
`κ(𝔭)` which is integral over `κ(𝔭)` (e.g. a generator of a finite separable extension). Then
there are `c ∈ R \ 𝔭` and a monic `f ∈ R[T]` whose image in `κ(𝔭)[T]` is the minimal polynomial of
`c α` over `κ(𝔭)` (blueprint: `lem-weil-pbc-etale-residue-polynomial-lift`). -/
theorem exists_monic_map_eq_minpoly {L : Type*} [Field L] [Algebra 𝔭.ResidueField L] {α : L}
    (hα : IsIntegral 𝔭.ResidueField α) :
    ∃ c ∉ 𝔭, ∃ f : R[X], f.Monic ∧ f.map (algebraMap R 𝔭.ResidueField) =
      minpoly 𝔭.ResidueField (algebraMap 𝔭.ResidueField L (algebraMap R _ c) * α) := by
  classical
  set κ := 𝔭.ResidueField
  set m := minpoly κ α
  choose s hs hsm using fun i ↦ exists_notMem_mul_mem_range 𝔭 (m.coeff i)
  set c := ∏ i ∈ Finset.range m.natDegree, s i
  have hc : c ∉ 𝔭 := by
    simp only [c, ← Ideal.mem_primeCompl_iff]
    exact Submonoid.prod_mem _ fun i _ ↦ hs i
  have hc0 : algebraMap R κ c ≠ 0 := by rwa [Ne, Ideal.algebraMap_residueField_eq_zero]
  refine ⟨c, hc, ?_⟩
  rw [← Algebra.smul_def, IsIntegrallyClosed.minpoly_smul hc0 hα]
  have hmon : (m.scaleRoots (algebraMap R κ c)).Monic := by
    simpa [Polynomial.monic_scaleRoots_iff] using minpoly.monic hα
  have hlifts : m.scaleRoots (algebraMap R κ c) ∈ lifts (algebraMap R κ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [coeff_scaleRoots]
    rcases lt_trichotomy n m.natDegree with hn | rfl | hn
    · obtain ⟨e, he⟩ : s n ∣ c := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hn)
      obtain ⟨a, ha⟩ := hsm n
      refine ⟨c ^ (m.natDegree - n - 1) * e * a, ?_⟩
      have : m.natDegree - n = m.natDegree - n - 1 + 1 := by omega
      have hce : algebraMap R κ c = algebraMap R κ (s n) * algebraMap R κ e := by
        rw [he, map_mul]
      rw [this, pow_succ, map_mul, map_mul, ha, map_pow, Nat.add_sub_cancel]
      linear_combination (-(algebraMap R κ c ^ (m.natDegree - n - 1) * m.coeff n)) * hce
    · exact ⟨1, by simpa [m] using (minpoly.monic hα).leadingCoeff.symm⟩
    · exact ⟨0, by simp [coeff_eq_zero_of_natDegree_lt hn]⟩
  obtain ⟨f, hf, -, hfm⟩ := lifts_and_natDegree_eq_and_monic hlifts hmon
  exact ⟨f, hfm, hf⟩

end Ideal.ResidueField
