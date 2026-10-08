/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Polynomial.IntegralNormalization

/-!
# Étale algebras realizing finite separable residue field extensions

Let `A` be a commutative ring, `p` a prime of `A` and `L` a finite separable extension of the
residue field `κ(p)`. We show that there is an étale `A`-algebra `A'` with a prime `P` lying
over `p` whose residue field is (compatibly) isomorphic to `L`.

## Main statements

- `Algebra.exists_monic_aeval_eq_zero_aeval_derivative_ne_zero`: for a domain `R` with fraction
  field `K` and a finite separable extension `L / K`, there is a monic polynomial `G ∈ R[X]` and
  a primitive element `β` of `L / K` which is a simple root of `G`.
- `Algebra.exists_etale_residueField_equiv`: the étale algebra realizing `L` as a residue field;
  it is the standard étale algebra `(A[X]/(F))[1/F']` for a monic lift `F` of `G`.

## Implementation notes

The primitive element `β'` given by the primitive element theorem has a minimal polynomial with
coefficients in `K` only. We clear denominators (`IsLocalization.integerNormalization`) and
normalize to a monic polynomial (`Polynomial.integralNormalization`); this replaces `β'` by
`c • β'` for a nonzero `c ∈ R`, which is still a primitive element. The resulting monic
`G ∈ R[X]` maps to the minimal polynomial of `β` over `K`, which is separable, so `β` is a
simple root of `G`.
-/

@[expose] public section

universe u v

open Polynomial IntermediateField

namespace Algebra

section Polynomial

variable {R K L : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

/-- For a domain `R` with fraction field `K` and a finite separable extension `L / K` there is
a monic polynomial `G ∈ R[X]` and a primitive element `β` of `L / K` that is a simple root of
`G`. -/
theorem exists_monic_aeval_eq_zero_aeval_derivative_ne_zero :
    ∃ (G : R[X]) (β : L), G.Monic ∧ K⟮β⟯ = ⊤ ∧ aeval β G = 0 ∧ aeval β (derivative G) ≠ 0 := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hinjL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp hinj
  obtain ⟨β', hβ'⟩ := Field.exists_primitive_element K L
  have hint : IsIntegral K β' := Algebra.IsIntegral.isIntegral (R := K) β'
  set m := minpoly K β' with hm_def
  have hm : m.Monic := minpoly.monic hint
  set N := IsLocalization.integerNormalization (nonZeroDivisors R) m with hN_def
  obtain ⟨b, hb, hbN⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) m
  have hb0 : algebraMap R K b ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]
    exact nonZeroDivisors.ne_zero hb
  have hNmap : N.map (algebraMap R K) ≠ 0 := by
    rw [hbN, ← algebraMap_smul K b m, smul_eq_C_mul, mul_ne_zero_iff, C_ne_zero]
    exact ⟨hb0, hm.ne_zero⟩
  have hN0 : N ≠ 0 := fun h ↦ hNmap (by simp [h])
  -- degree bookkeeping
  have hdegN : N.natDegree = m.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj N, hbN, ← algebraMap_smul K b m, smul_eq_C_mul,
      natDegree_C_mul hb0]
  set G := N.integralNormalization with hG_def
  have hG : G.Monic := monic_integralNormalization hN0
  have hdegG : G.natDegree = m.natDegree := by rw [hG_def, natDegree_integralNormalization, hdegN]
  -- the new primitive element
  set c : R := N.leadingCoeff with hc_def
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hN0
  set β : L := algebraMap R L c * β' with hβ_def
  have hNβ' : aeval β' N = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors R) m (minpoly.aeval K β')
  have hGβ : aeval β G = 0 :=
    integralNormalization_aeval_eq_zero hNβ' fun x hx ↦ hinjL (by simpa using hx)
  have hβ_top : K⟮β⟯ = ⊤ := by
    rw [← top_le_iff, ← hβ', IntermediateField.adjoin_simple_le_iff]
    have hcK : algebraMap K L (algebraMap R K c) ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap K L).injective, map_ne_zero_iff _ hinj]
      exact hc0
    have : β' = algebraMap K L (algebraMap R K c)⁻¹ * β := by
      rw [hβ_def, IsScalarTower.algebraMap_apply R K L, ← mul_assoc, map_inv₀,
        inv_mul_cancel₀ hcK, one_mul]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self _ _)
  -- `G` maps to the minimal polynomial of `β` over `K`
  have hintβ : IsIntegral K β := Algebra.IsIntegral.isIntegral (R := K) β
  have hGmin : G.map (algebraMap R K) = minpoly K β := by
    refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintβ) (hG.map _) ?_ ?_
    · refine minpoly.dvd K β ?_
      rw [aeval_map_algebraMap, hGβ]
    · rw [natDegree_map_eq_of_injective hinj, hdegG, hm_def,
        ← IntermediateField.adjoin.finrank hint,
        ← IntermediateField.adjoin.finrank hintβ, hβ', hβ_top]
  have hsep : (G.map (algebraMap R K)).Separable := hGmin ▸ Algebra.IsSeparable.isSeparable K β
  refine ⟨G, β, hG, hβ_top, hGβ, ?_⟩
  have := hsep.aeval_derivative_ne_zero (x := β) (by rw [aeval_map_algebraMap, hGβ])
  rwa [derivative_map, aeval_map_algebraMap] at this

end Polynomial

section Etale

variable {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]

/-- Given a prime `p` of `A` and a finite separable extension `L` of `κ(p)`, there is an étale
`A`-algebra `A'` with a prime `P` lying over `p` whose residue field is `L`, compatibly with the
inclusion `κ(p) → L`. -/
theorem exists_etale_residueField_equiv
    (L : Type v) [Field L] [Algebra p.ResidueField L] [FiniteDimensional p.ResidueField L]
    [Algebra.IsSeparable p.ResidueField L] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (P : Ideal A') (_ : P.IsPrime) (hP : p = P.comap (algebraMap A A')),
      ∃ e : P.ResidueField ≃+* L,
        ∀ x, e (Ideal.ResidueField.map p P (algebraMap A A') hP x) =
          algebraMap p.ResidueField L x := by
  classical
  -- Set up `L` as an algebra over `A ⧸ p` and over `A`.
  let _ : Algebra (A ⧸ p) L := ((algebraMap p.ResidueField L).comp (algebraMap (A ⧸ p) _)).toAlgebra
  have : IsScalarTower (A ⧸ p) p.ResidueField L := .of_algebraMap_eq fun _ ↦ rfl
  let _ : Algebra A L := ((algebraMap (A ⧸ p) L).comp (algebraMap A (A ⧸ p))).toAlgebra
  have : IsScalarTower A (A ⧸ p) L := .of_algebraMap_eq fun _ ↦ rfl
  have hAL : algebraMap A L = (algebraMap p.ResidueField L).comp (algebraMap A p.ResidueField) := by
    rw [IsScalarTower.algebraMap_eq A (A ⧸ p) p.ResidueField]; rfl
  obtain ⟨G, β, hG, hβ, hGβ, hG'β⟩ :=
    exists_monic_aeval_eq_zero_aeval_derivative_ne_zero (R := A ⧸ p) (K := p.ResidueField) (L := L)
  -- Lift `G` to a monic polynomial over `A`.
  obtain ⟨F, hFG, -, hF⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts _).mpr (map_surjective _ Ideal.Quotient.mk_surjective G)) hG
  have hFβ : aeval β F = 0 := by
    rw [aeval_def, IsScalarTower.algebraMap_eq A (A ⧸ p) L, ← eval₂_map, ← aeval_def]
    rw [show Ideal.Quotient.mk p = algebraMap A (A ⧸ p) from rfl] at hFG
    rw [hFG, hGβ]
  have hF'β : aeval β (derivative F) ≠ 0 := by
    rw [aeval_def, IsScalarTower.algebraMap_eq A (A ⧸ p) L, ← eval₂_map, ← derivative_map,
      ← aeval_def]
    rw [show Ideal.Quotient.mk p = algebraMap A (A ⧸ p) from rfl] at hFG
    rwa [hFG]
  -- The standard étale algebra `(A[X]/(F))[1/F']`.
  let S : StandardEtalePair A := ⟨F, hF, derivative F, ⟨1, 0, 1, by simp⟩⟩
  have hmap : S.HasMap β := ⟨hFβ, hF'β.isUnit⟩
  let φ : S.Ring →ₐ[A] L := S.lift β hmap
  have hφX : φ S.X = β := S.lift_X β hmap
  let P : Ideal S.Ring := RingHom.ker φ
  have : P.IsPrime := RingHom.ker_isPrime _
  have hP : p = P.comap (algebraMap A S.Ring) := by
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker, φ.commutes, hAL, RingHom.comp_apply,
      map_eq_zero_iff (algebraMap p.ResidueField L) (algebraMap p.ResidueField L).injective,
      Ideal.algebraMap_residueField_eq_zero]
  -- The residue field of `P` maps to `L`.
  let e : P.ResidueField →+* L := Ideal.ResidueField.lift P φ.toRingHom le_rfl fun x hx ↦
    isUnit_iff_ne_zero.mpr (by simpa [P, RingHom.mem_ker] using hx)
  have he : ∀ x, e (algebraMap S.Ring _ x) = φ x := fun x ↦
    Ideal.ResidueField.lift_algebraMap P φ.toRingHom _ _ x
  have hcomp : ∀ x, e (Ideal.ResidueField.map p P (algebraMap A S.Ring) hP x) =
      algebraMap p.ResidueField L x := by
    suffices e.comp (Ideal.ResidueField.map p P (algebraMap A S.Ring) hP) =
        algebraMap p.ResidueField L from fun x ↦ congr($this x)
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap, he]
    rw [φ.commutes, hAL]
    rfl
  -- `e` is bijective.
  have hsurj : Function.Surjective e := by
    let T : IntermediateField p.ResidueField L :=
      e.fieldRange.toIntermediateField fun x ↦ ⟨_, hcomp x⟩
    have hT : T = ⊤ := by
      rw [← top_le_iff, ← hβ, IntermediateField.adjoin_simple_le_iff]
      exact ⟨algebraMap S.Ring _ S.X, by rw [he, hφX]⟩
    intro y
    have : y ∈ T := hT ▸ IntermediateField.mem_top
    exact this
  exact ⟨S.Ring, inferInstance, inferInstance, inferInstance, P, inferInstance, hP,
    RingEquiv.ofBijective e ⟨e.injective, hsurj⟩, hcomp⟩

end Etale

end Algebra
