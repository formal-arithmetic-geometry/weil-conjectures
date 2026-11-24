/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

import WeilConjectures.RingTheory.FiniteRankDefectDerivation

/-!
# Finite-rank correction of a lifted coefficient section

Two ring maps `k → Λ` agreeing modulo an ideal `I` killed by the maximal ideal differ by a
derivation; after correcting the residue section `K → Λ` by a derivation `K → I`, the remaining
discrepancy lies in the `k`-span of finitely many elements of `I`.

## Implementation details

The difference `θ = algebraMap k Λ - ψ` is a derivation with values in `I`. Using
Jacobi–Zariski exactness and finite dimensionality of `H1Cotangent k K`, a derivation
`D : K → I` is chosen so that `θ - D|k` has finite rank, and the new section is
`σ = σ0 + D`.

## References

* Stacks Project, Tag 07FG, the derivation and Jacobi–Zariski paragraphs.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- Given two structure maps agreeing modulo an annihilated ideal `I`, an existing residue
section can be adjusted so that their discrepancy lies in the `k`-span of finitely many
elements of `I`. The fixed coefficient field is not enlarged. -/
theorem exists_finite_rank_coefficient_correction
    (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]
    (Λ : Type v) [CommRing Λ] [Algebra k Λ] [IsLocalRing Λ]
    (r : Λ →+* K) (hker : RingHom.ker r = IsLocalRing.maximalIdeal Λ)
    (hcomm : r.comp (algebraMap k Λ) = algebraMap k K)
    (t : Finset Λ) (ht : Ideal.span (t : Set Λ) = IsLocalRing.maximalIdeal Λ)
    (I : Ideal Λ) (hI : I ≤ RingHom.ker r)
    (hkill : IsLocalRing.maximalIdeal Λ * I = ⊥)
    (σ0 : K →+* Λ) (hσ0 : r.comp σ0 = RingHom.id K) (c0 : Finset K)
    (ψ : k →+* Λ)
    (hψ : (Ideal.Quotient.mk I).comp ψ =
      (Ideal.Quotient.mk I).comp (algebraMap k Λ))
    (hψmem : ∀ a : k, ψ a ∈ Subring.closure ((t : Set Λ) ∪
      σ0 '' (IntermediateField.adjoin k (c0 : Set K) : Set K)))
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (hH : Module.Finite K (H1Cotangent k K)) :
    ∃ (σ : K →+* Λ) (f : Finset Λ),
      r.comp σ = RingHom.id K ∧
      (Ideal.Quotient.mk I).comp σ = (Ideal.Quotient.mk I).comp σ0 ∧
      (f : Set Λ) ⊆ I ∧
      (∀ a : k, ∃ b : Λ,
        b ∈ Subring.closure ((t : Set Λ) ∪
          σ '' (IntermediateField.adjoin k (c0 : Set K) : Set K)) ∧
        algebraMap k Λ a - b ∈ Submodule.span k (f : Set Λ)) := by
  classical
  have hkill' : RingHom.ker r * I = ⊥ := by simpa [hker] using hkill
  have hzero {x y : Λ} (hx : x ∈ RingHom.ker r) (hy : y ∈ I) : x * y = 0 := by
    have hm := Ideal.mul_mem_mul hx hy
    rw [hkill'] at hm
    exact hm
  let theta : k →+ Λ := (algebraMap k Λ).toAddMonoidHom - ψ.toAddMonoidHom
  have htheta (a : k) : theta a ∈ I := by
    change algebraMap k Λ a - ψ a ∈ I
    apply Ideal.Quotient.eq.mp
    exact (RingHom.congr_fun hψ a).symm
  have htheta_one : theta 1 = 0 := by simp [theta]
  have htheta_mul (a b : k) :
      theta (a * b) = algebraMap k Λ a * theta b + algebraMap k Λ b * theta a := by
    have hz := hzero (hI (htheta a)) (htheta b)
    dsimp [theta] at hz ⊢
    simp only [map_mul]
    linear_combination -hz
  obtain ⟨D, f, hD1, hDmul, hDI, hfI, herr⟩ := exists_finite_rank_defect_derivation
    k K Λ r hcomm I hI hkill' σ0 hσ0 theta htheta htheta_one htheta_mul p hp hH
  have hrσ (x : K) : r (σ0 x) = x := RingHom.congr_fun hσ0 x
  have hrD (x : K) : r (D x) = 0 := RingHom.mem_ker.mp (hI (hDI x))
  have hact (x y : Λ) : σ0 (r x) * D (r y) = x * D (r y) := by
    have hx : σ0 (r x) - x ∈ RingHom.ker r := by
      rw [RingHom.mem_ker, map_sub, hrσ, sub_self]
    have hz := hzero hx (hDI (r y))
    linear_combination hz
  -- This ring endomorphism simultaneously adjusts every coefficient expression.
  let β : Λ →+* Λ :=
    { toFun := fun x ↦ x + D (r x)
      map_one' := by simp [hD1]
      map_zero' := by simp
      map_add' := by intros; simp only [map_add]; abel
      map_mul' := by
        intro x y
        have hz := hzero (hI (hDI (r x))) (hDI (r y))
        simp only [map_mul, hDmul]
        rw [hact x y, hact y x]
        linear_combination -hz }
  let σ := β.comp σ0
  have hσ_apply (x : K) : σ x = σ0 x + D x := by
    change σ0 x + D (r (σ0 x)) = _
    rw [hrσ]
  have hσ : r.comp σ = RingHom.id K := by
    ext x
    simp [hσ_apply, hrσ, hrD]
  have hσq : (Ideal.Quotient.mk I).comp σ = (Ideal.Quotient.mk I).comp σ0 := by
    ext x
    simp only [RingHom.comp_apply, hσ_apply, map_add]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hDI x), add_zero]
  refine ⟨σ, f, hσ, hσq, hfI, ?_⟩
  intro a
  have hrψ (a : k) : r (ψ a) = algebraMap k K a := by
    have hz := RingHom.mem_ker.mp (hI (htheta a))
    change r (algebraMap k Λ a - ψ a) = 0 at hz
    have hc := RingHom.congr_fun hcomm a
    simp only [RingHom.comp_apply] at hc
    rw [map_sub, hc, sub_eq_zero] at hz
    exact hz.symm
  let S := Subring.closure ((t : Set Λ) ∪
    σ '' (IntermediateField.adjoin k (c0 : Set K) : Set K))
  have hβmem {x : Λ}
      (hx : x ∈ Subring.closure ((t : Set Λ) ∪
        σ0 '' (IntermediateField.adjoin k (c0 : Set K) : Set K))) : β x ∈ S := by
    change x ∈ S.comap β
    apply (Subring.closure_le (t := S.comap β)).mpr ?_ hx
    intro x hx
    change β x ∈ S
    rcases hx with hx | ⟨y, hy, rfl⟩
    · have hxt : x ∈ RingHom.ker r := by
        rw [hker, ← ht]
        exact Ideal.subset_span hx
      have hβx : β x = x := by
        change x + D (r x) = x
        simp [RingHom.mem_ker.mp hxt]
      rw [hβx]
      exact Subring.subset_closure (Or.inl hx)
    · exact Subring.subset_closure (Or.inr ⟨y, hy, rfl⟩)
  refine ⟨β (ψ a), hβmem (hψmem a), ?_⟩
  have he := herr a
  change algebraMap k Λ a - (ψ a + D (r (ψ a))) ∈ Submodule.span k (f : Set Λ)
  rw [hrψ]
  convert he using 1
  dsimp [theta]
  abel

end Algebra
