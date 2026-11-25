/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Surjectivity of a finite coefficient tensor map modulo the model maximal ideal

For local rings with `A` finite over `A₀`, surjectivity of `C → B / m_A B` implies surjectivity
of the tensor map `C ⊗[A₀] A → B / m_C B`.

## Implementation details

The closed fibre `A / m₀ A` is Artinian local, so `m_A ^ N ⊆ m₀ A` for some `N > 0`. Induction
gives `B = F(D) + m_A ^ N B`, and `m_A ^ N B ⊆ m₀ B ⊆ m_C B` because `γ` is local. Neither
completeness nor flatness is used.

## References

* [Stacks, Remark 07NS] (1), (3)
-/

@[expose] public section

universe u v w z

namespace RingHom

-- Step 1: the finite closed fibre is Artinian, so its maximal ideal is nilpotent.
private theorem finite_local_power
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [Module.Finite R S]
    [IsLocalHom (algebraMap R S)] :
    ∃ n : ℕ, IsLocalRing.maximalIdeal S ^ n ≤
      (IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  have hI : I ≤ IsLocalRing.maximalIdeal S :=
    Ideal.map_le_iff_le_comap.mpr (by
      rw [IsLocalRing.maximalIdeal_comap])
  have : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hI)
  have : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : Algebra (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ I) := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    rfl
  have : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ I) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have : IsArtinianRing (S ⧸ I) :=
    IsArtinianRing.of_finite (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ I)
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal (S ⧸ I)).mp
    inferInstance
  refine ⟨n, ?_⟩
  have hm : (IsLocalRing.maximalIdeal S ^ n).map (Ideal.Quotient.mk I) = ⊥ := by
    rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective]
    exact hn
  have hle := Ideal.map_le_iff_le_comap.mp (le_of_eq hm)
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hle

/-- If `C → B / m_A B` is surjective and `A` is finite over `A₀`, then `C ⊗[A₀] A → B / m_C B`
is surjective. -/
theorem finite_coefficient_tensor_reduction_surjective
    {A₀ : Type u} {A : Type v} {B : Type w} {C : Type z}
    [CommRing A₀] [CommRing A] [CommRing B] [CommRing C]
    [Algebra A₀ A] [Algebra A₀ C]
    [IsLocalRing A₀] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    (α : A₀ →+* A) (hα : algebraMap A₀ A = α) [IsLocalHom α]
    [Module.Finite A₀ A]
    (γ : A₀ →+* C) (hγ : algebraMap A₀ C = γ) [IsLocalHom γ]
    (φ : A →+* B) [IsLocalHom φ]
    (ψ : C →+* B) [IsLocalHom ψ] (hψγ : ψ.comp γ = φ.comp α)
    (F : TensorProduct A₀ C A →+* B)
    (hF : ∀ c a, F (TensorProduct.tmul A₀ c a) = ψ c * φ a)
    (hres : Function.Surjective
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ)).comp ψ)) :
    Function.Surjective
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal C).map ψ)).comp F) := by
  have : IsLocalHom (algebraMap A₀ A) := hα.symm ▸ ‹IsLocalHom α›
  have : IsLocalHom (algebraMap A₀ C) := hγ.symm ▸ ‹IsLocalHom γ›
  obtain ⟨n, hn⟩ := finite_local_power (R := A₀) (S := A)
  rw [hα] at hn
  let : Algebra A B := φ.toAlgebra
  let : Algebra A (TensorProduct A₀ C A) := Algebra.TensorProduct.rightAlgebra
  let f : TensorProduct A₀ C A →ₐ[A] B :=
    { F with
      commutes' := fun a ↦ by
        change F (TensorProduct.tmul A₀ 1 a) = φ a
        simpa using hF 1 a }
  let L := f.toLinearMap.range
  let I := IsLocalRing.maximalIdeal A
  let J := (IsLocalRing.maximalIdeal C).map ψ
  have hψ : ∀ c, ψ c ∈ L := by
    intro c
    exact ⟨TensorProduct.tmul A₀ c 1, by simpa [f] using hF c 1⟩
  have hbase : (I • ⊤ : Submodule A B) ⊔ L = ⊤ := by
    apply top_unique
    intro b _
    obtain ⟨c, hc⟩ := hres (Ideal.Quotient.mk (I.map φ) b)
    have hb : b - ψ c ∈ I.map φ := by
      apply Ideal.Quotient.eq.mp
      exact hc.symm
    apply Submodule.mem_sup.mpr
    refine ⟨b - ψ c, ?_, ψ c, hψ c, sub_add_cancel _ _⟩
    rw [Ideal.smul_top_eq_map]
    exact hb
  have hpow : ∀ k : ℕ, (I ^ k • ⊤ : Submodule A B) ⊔ L = ⊤ := by
    intro k
    induction k with
    | zero =>
        rw [pow_zero, one_smul, top_sup_eq]
    | succ k ih =>
      calc
        (I ^ (k + 1) • ⊤ : Submodule A B) ⊔ L =
            I ^ k • (I • ⊤ : Submodule A B) ⊔ L := by
          rw [pow_succ, Submodule.mul_smul]
        _ = I ^ k • ((I • ⊤ : Submodule A B) ⊔ L) ⊔ L := by
          rw [Submodule.smul_sup, sup_assoc,
            sup_of_le_right (Submodule.smul_le_right (I := I ^ k) (N := L))]
        _ = (I ^ k • ⊤ : Submodule A B) ⊔ L := by rw [hbase]
        _ = ⊤ := ih
  have hsmall : (I ^ n • ⊤ : Submodule A B) ≤ J.restrictScalars A := by
    rw [Ideal.smul_top_eq_map]
    change (I ^ n).map φ ≤ J
    apply le_trans (Ideal.map_mono hn)
    rw [Ideal.map_map, ← hψγ, ← Ideal.map_map]
    apply Ideal.map_mono
    rw [← hγ]
    exact Ideal.map_le_iff_le_comap.mpr (by rw [IsLocalRing.maximalIdeal_comap])
  intro q
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hb : b ∈ (I ^ n • ⊤ : Submodule A B) ⊔ L := by rw [hpow]; trivial
  obtain ⟨r, hr, t, ht, hrt⟩ := Submodule.mem_sup.mp hb
  obtain ⟨d, rfl⟩ := ht
  refine ⟨d, ?_⟩
  apply Ideal.Quotient.eq.mpr
  have heq : f d - b = -r := by rw [← hrt]; simp
  change f d - b ∈ J
  rw [heq]
  exact J.neg_mem (hsmall hr)

end RingHom
