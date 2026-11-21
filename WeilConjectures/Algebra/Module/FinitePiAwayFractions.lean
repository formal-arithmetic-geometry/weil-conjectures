/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Coordinate fractions and finite products

## References

* [Stacks Project, Tag 00JM](https://stacks.math.columbia.edu/tag/00JM), common denominator
  argument for finite sums
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7), part (2)
-/

@[expose] public section

universe v

namespace LocalizedModule

/-- The coordinate map from a localized finite power to the power of the localization.
-/
noncomputable def awayPi {A : Type v} [CommRing A] (r : ℕ) (f : A) :
    LocalizedModule.Away f (Fin r → A) →ₗ[A] (Fin r → LocalizedModule.Away f A) :=
  LinearMap.pi fun i ↦ IsLocalizedModule.map (Submonoid.powers f)
    (mkLinearMap (Submonoid.powers f) (Fin r → A))
    (mkLinearMap (Submonoid.powers f) A) (LinearMap.proj i)

/-- The coordinate map `awayPi` sends the fraction `y / s` to the tuple of fractions
`y i / s`. -/
@[simp]
theorem awayPi_mk {A : Type v} [CommRing A] (r : ℕ) (f : A)
    (y : Fin r → A) (s : Submonoid.powers f) (i : Fin r) :
    awayPi r f (mk y s) i = mk (y i) s := by
  exact IsLocalizedModule.map_LocalizedModules _ _ _ _

/-- The coordinate map `awayPi` commutes with scalar multiplication by `Localization.Away f`. -/
theorem awayPi_smul {A : Type v} [CommRing A] (r : ℕ) (f : A)
    (q : Localization.Away f) (x : LocalizedModule.Away f (Fin r → A)) :
    awayPi r f (q • x) = q • awayPi r f x := by
  induction x using LocalizedModule.induction_on with
  | h y s =>
    induction q using Localization.induction_on with
    | H z =>
      rcases z with ⟨u, t⟩
      ext i
      simp only [mk_smul_mk, awayPi_mk, Pi.smul_apply]

/-- Localization commutes with finite powers, without any homogeneity assumption.
-/
theorem awayPi_bijective {A : Type v} [CommRing A] (r : ℕ) (f : A) :
    Function.Bijective (awayPi r f) := by
  let S := Submonoid.powers f
  let g : (Fin r → A) →ₗ[A] (Fin r → LocalizedModule.Away f A) :=
    LinearMap.pi fun i ↦ (mkLinearMap S A).comp (LinearMap.proj i)
  have : IsLocalizedModule S g := IsLocalizedModule.pi S (fun _ : Fin r ↦ mkLinearMap S A)
  have heq : awayPi r f = (IsLocalizedModule.iso S g).toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S (mkLinearMap S (Fin r → A)) g
    apply LinearMap.ext
    intro y
    change awayPi r f (mk y 1) = IsLocalizedModule.iso S g (mk y 1)
    rw [IsLocalizedModule.iso_mk_one]
    ext i
    exact awayPi_mk r f y 1 i
  rw [heq]
  exact (IsLocalizedModule.iso S g).bijective

/-- Localization of a finite power is its coordinate product, and equal-degree fractions
are exactly those whose coordinates are equal-degree fractions for the individual shifts. -/
theorem awayPi_bijective_degreeZero
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (r : ℕ) (a : Fin r → ℤ)
    (f : A) :
    Function.Bijective (awayPi r f) ∧
    ∀ x : LocalizedModule.Away f (Fin r → A),
      x ∈ degreeZeroFractions (fun n : ℕ ↦ (𝒜 n : Set A))
        (fun n : ℕ ↦ {y : Fin r → A | ∀ i,
          if 0 ≤ a i + n then y i ∈ 𝒜 (a i + n).toNat else y i = 0})
        (Submonoid.powers f) ↔
      ∀ i, awayPi r f x i ∈ degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set A))
        (fun n : ℕ ↦ {y : A |
          if 0 ≤ a i + n then y ∈ 𝒜 (a i + n).toNat else y = 0})
        (Submonoid.powers f) := by
  classical
  refine ⟨awayPi_bijective r f, ?_⟩
  intro x
  constructor
  · rintro ⟨d, y, s, hy, hs, rfl⟩ i
    exact ⟨d, y i, s, hy i, hs, (awayPi_mk r f y s i).symm⟩
  · intro hx
    choose d y s hy hs heq using hx
    let D : ℕ := ∑ i, d i
    let t : Submonoid.powers f := ∏ i, s i
    let u (i : Fin r) : Submonoid.powers f := ∏ j ∈ Finset.univ.erase i, s j
    let z (i : Fin r) : A := (u i : A) * y i
    have hd (i : Fin r) : (∑ j ∈ Finset.univ.erase i, d j) + d i = D :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have ht (i : Fin r) : u i * s i = t :=
      Finset.prod_erase_mul _ _ (Finset.mem_univ i)
    have hu (i : Fin r) : (u i : A) ∈ 𝒜 (∑ j ∈ Finset.univ.erase i, d j) := by
      simpa [u] using SetLike.prod_mem_graded 𝒜 d
        (fun j ↦ (s j : A)) (fun j _ ↦ hs j)
    have hz (i : Fin r) :
        if 0 ≤ a i + D then z i ∈ 𝒜 (a i + D).toNat else z i = 0 := by
      by_cases hi : 0 ≤ a i + d i
      · have hyi : y i ∈ 𝒜 (a i + d i).toNat := by simpa [hi] using hy i
        have hdi : d i ≤ D := by have := hd i; omega
        have hD : 0 ≤ a i + D := by omega
        simp only [hD, ↓reduceIte]
        have hdeg : (∑ j ∈ Finset.univ.erase i, d j) + (a i + d i).toNat =
            (a i + D).toNat := by
          have := hd i
          omega
        simpa only [z, hdeg] using SetLike.mul_mem_graded (hu i) hyi
      · have hyi : y i = 0 := by simpa [hi] using hy i
        simp only [z, hyi, mul_zero]
        split <;> simp
    have htmem : (t : A) ∈ 𝒜 D := by
      simpa [t, D] using SetLike.prod_mem_graded 𝒜 d
        (fun j ↦ (s j : A)) (fun j _ ↦ hs j)
    refine ⟨D, z, t, hz, htmem, (awayPi_bijective r f).1 ?_⟩
    ext i
    rw [awayPi_mk, ← heq i, ← ht i]
    exact mk_cancel_common_left (u i) (s i) (y i)


end LocalizedModule
