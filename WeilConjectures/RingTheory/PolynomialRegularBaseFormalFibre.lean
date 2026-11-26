/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.Algebra.Polynomial.Derivation
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization
import WeilConjectures.RingTheory.HypersurfaceDerivationRegular
import WeilConjectures.RingTheory.PolynomialNonzeroFibreHypersurface

/-!
# Regular polynomial formal fibres over a regular local base in characteristic zero

For a regular local ring `A` of characteristic zero and a maximal ideal `q` of `A[X]`, the
formal fibres of `A[X]_q` over primes above zero are regular.

## Implementation details

The completion `C` of `A[X]_q` is regular (Tags 07NY, 0AFS). The zero fibre is a localization of
`C`; a nonzero fibre is `R / (f)` with `R` a localization of `C` and `f` irreducible, and the
derivation `d/dX` (Tag 07PE) makes it regular by the hypersurface criterion (Tag 07PF) since
`f` and `f'` are coprime. No completeness assumption on `A` is needed.

## References

* [Stacks, Tag 07PV] (paragraphs 3–4 of the proof)
* [Stacks, Tag 07PU]
* [Stacks, Tag 07NY]
* [Stacks, Tag 0AFS]
* [Stacks, Tag 07PE]
* [Stacks, Tag 07PF]
-/

@[expose] public section

universe u

private theorem regular_localization {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsRegularRing R] (M : Submonoid R) [IsLocalization M S] :
    IsRegularRing S := by
  apply RingTheory.isRegularRing_of_localization R S M (algebraMap R S)
  · exact IsLocalization.map_units S
  · intro y
    obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj M y
    obtain ⟨z, hz⟩ := IsLocalization.map_units S s
    refine ⟨r, s, ↑z⁻¹, z⁻¹.isUnit, ?_, ?_⟩
    · rw [← hz]
      exact z.mul_inv
    · calc
        y = (y * algebraMap R S s) * ↑z⁻¹ := by rw [← hz]; simp
        _ = algebraMap R S r * ↑z⁻¹ := by rw [hy]
  · intro r hr
    exact (IsLocalization.map_eq_zero_iff M S r).mp hr

private def intDerivationOfLeibniz (R : Type u) [CommRing R] (d : R → R)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = a * d b + b * d a) : Derivation ℤ R R :=
  Derivation.mk'
    { toFun := d
      map_add' := hadd
      map_smul' := fun n a ↦ by
        let f : R →+ R :=
          { toFun := d, map_add' := hadd, map_zero' := by
              simpa using (hadd 0 0).symm }
        exact map_zsmul f n a }
    (fun a b ↦ by
      change d (a * b) = a * d b + b * d a
      exact hmul a b)

namespace Polynomial

/-- The formal fibre above zero over a characteristic-zero regular local base is regular. -/
theorem regularBase_formalFibre_isRegular
    (A : Type u) [CommRing A] [IsRegularLocalRing A] [CharZero A]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    IsRegularRing (r.Fiber
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q))) := by
  let B := Localization.AtPrime q
  let C := AdicCompletion (IsLocalRing.maximalIdeal B) B
  have : IsRegularLocalRing B :=
    isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal A q hq
  have : IsRegularLocalRing C := (AdicCompletion.isRegularLocalRing_iff B).mp ‹_›
  have : IsRegularRing C :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal C)).2
  by_cases hr : r = ⊥
  · subst r
    let M := Algebra.algebraMapSubmonoid C (⊥ : Ideal (Polynomial A)).primeCompl
    have : IsRegularRing (Localization M) := regular_localization M
    let : Algebra C ((⊥ : Ideal (Polynomial A)).Fiber C) :=
      Algebra.TensorProduct.rightAlgebra
    let e := Ideal.Fiber.algEquivAux₁ (S := C) (⊥ : Ideal (Polynomial A))
    have hbot :
        ((⊥ : Ideal (Polynomial A)).map (algebraMap (Polynomial A) C)).map
          (algebraMap C (Localization M)) = ⊥ := by simp
    let e' := e.toRingEquiv.trans
      ((Ideal.quotientEquivAlgOfEq C hbot).toRingEquiv.trans
        (RingEquiv.quotientBot _))
    exact IsRegularRing.of_ringEquiv e'.symm
  · let M := Submonoid.map
      ((algebraMap (Polynomial A) C).comp Polynomial.C).toMonoidHom (nonZeroDivisors A)
    let R := Localization M
    have : IsRegularRing R := regular_localization M
    obtain ⟨f, ⟨e⟩, hunit⟩ := nonzero_fibre_hypersurface_presentation A C r hr hrA
    let D₀ : Derivation ℤ (Polynomial A) (Polynomial A) := derivative'.restrictScalars ℤ
    obtain ⟨D₁, hD₁, _, _⟩ :=
      (Derivation.exists_completion_and_unique_localization (Polynomial A) D₀).2 q.primeCompl
    let D₁' := intDerivationOfLeibniz B (fun x ↦ D₁ x)
      (fun a b ↦ D₁.map_add a b) (fun a b ↦ by
        simpa only [smul_eq_mul] using D₁.leibniz a b)
    obtain ⟨D₂, _, hD₂, _, _⟩ :=
      (Derivation.exists_completion_and_unique_localization B D₁').1
        (IsLocalRing.maximalIdeal B)
    obtain ⟨D₃, hD₃, _, _⟩ :=
      (Derivation.exists_completion_and_unique_localization C D₂).2 M
    let : Algebra ℤ C := Ring.toIntAlgebra C
    let D₃' := intDerivationOfLeibniz R (fun x ↦ D₃ x)
      (fun a b ↦ D₃.map_add a b) (fun a b ↦ by
        simpa only [smul_eq_mul] using D₃.leibniz a b)
    have hDf : D₃' (algebraMap (Polynomial A) R f) =
        algebraMap (Polynomial A) R (derivative f) := by
      change D₃ (algebraMap (Polynomial A) R f) = _
      rw [IsScalarTower.algebraMap_apply (Polynomial A) C R, hD₃,
        IsScalarTower.algebraMap_apply (Polynomial A) B C, hD₂]
      change algebraMap C R (algebraMap B C (D₁ (algebraMap (Polynomial A) B f))) = _
      rw [hD₁]
      rfl
    have : IsRegularRing
        (R ⧸ Ideal.span ({algebraMap (Polynomial A) R f} : Set R)) :=
      IsRegularRing.quotient_span_singleton_of_isUnit_derivation R
        (algebraMap (Polynomial A) R f) D₃' (by rw [hDf]; exact hunit)
    exact IsRegularRing.of_ringEquiv e.symm

end Polynomial
