/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Profinite
import WeilConjectures.FieldTheory.TensorFieldExtensionGaloisInvariants

/-!
# Galois orbits of primes in a scalar extension

## References

* [Stacks Project, Tag 038B](https://stacks.math.columbia.edu/tag/038B)
-/

@[expose] public section

universe u

open scoped TensorProduct Pointwise

namespace Algebra.TensorProduct

/-- Primes of a scalar extension with equal contractions differ by an automorphism
of the extension field. -/
theorem exists_comap_eq_of_galois
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (A : Type u) [CommRing A] [Algebra k A]
    (x y : PrimeSpectrum (A ⊗[k] K))
    (hxy : PrimeSpectrum.comap
      (includeLeft : A →ₐ[k] A ⊗[k] K).toRingHom x =
      PrimeSpectrum.comap (includeLeft : A →ₐ[k] A ⊗[k] K).toRingHom y) :
    ∃ σ : K ≃ₐ[k] K,
      PrimeSpectrum.comap (map (AlgHom.id k A) σ.toAlgHom).toRingHom x = y := by
  classical
  let B := A ⊗[k] K
  let ρ : (K ≃ₐ[k] K) →* (B ≃ₐ[k] B) :=
    { toFun := fun σ ↦ congr (AlgEquiv.refl : A ≃ₐ[k] A) σ
      map_one' := by
        change congr (AlgEquiv.refl : A ≃ₐ[k] A) (AlgEquiv.refl : K ≃ₐ[k] K) = _
        exact congr_refl
      map_mul' := by
        intro σ τ
        ext z
        change map (AlgHom.id k A) (σ * τ).toAlgHom z =
          map (AlgHom.id k A) σ.toAlgHom (map (AlgHom.id k A) τ.toAlgHom z)
        induction z using TensorProduct.inductionOn with
        | tmul a t => simp
        | add z w hz hw => simp [hz, hw] }
  let : MulSemiringAction (K ≃ₐ[k] K) B := MulSemiringAction.compHom B ρ
  have hsmul (σ : K ≃ₐ[k] K) (z : B) :
      σ • z = map (AlgHom.id k A) σ.toAlgHom z := rfl
  let : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have hopen (z : B) : IsOpen (MulAction.stabilizer (K ≃ₐ[k] K) z : Set (K ≃ₐ[k] K)) := by
    induction z using TensorProduct.inductionOn with
    | tmul a t =>
      apply Subgroup.isOpen_mono ?_ (stabilizer_isOpen_of_isIntegral t)
      intro σ hσ
      change σ • (a ⊗ₜ[k] t) = a ⊗ₜ[k] t
      rw [hsmul]
      change a ⊗ₜ[k] σ t = a ⊗ₜ[k] t
      exact congrArg (fun t ↦ a ⊗ₜ[k] t) hσ
    | add z w hz hw =>
      apply Subgroup.isOpen_mono (H₁ :=
        (MulAction.stabilizer (K ≃ₐ[k] K) z) ⊓ MulAction.stabilizer (K ≃ₐ[k] K) w)
        ?_ (hz.inter hw)
      intro σ hσ
      change σ • (z + w) = z + w
      rw [smul_add, hσ.1, hσ.2]
  have : ContinuousSMul (K ≃ₐ[k] K) B :=
    continuousSMul_iff_stabilizer_isOpen.mpr hopen
  have : SMulCommClass (K ≃ₐ[k] K) A B := by
    constructor
    intro σ a z
    change map (AlgHom.id k A) σ.toAlgHom (a • z) =
      a • map (AlgHom.id k A) σ.toAlgHom z
    induction z using TensorProduct.inductionOn with
    | tmul a' t =>
      change map (AlgHom.id k A) σ.toAlgHom ((a * a') ⊗ₜ[k] t) =
        (a * a') ⊗ₜ[k] σ t
      rfl
    | add z w hz hw => simp [smul_add, hz, hw]
  have hfixed : {t : K | ∀ σ : (⊤ : Subgroup (K ≃ₐ[k] K)),
      (σ : K ≃ₐ[k] K) t = t} = Set.range (algebraMap k K) := by
    ext t
    simp only [Set.mem_ofPred, InfiniteGalois.mem_range_algebraMap_iff_fixed]
    exact ⟨fun h σ ↦ h ⟨σ, Subgroup.mem_top σ⟩, fun h σ ↦ h σ⟩
  have : Algebra.IsInvariant A B (K ≃ₐ[k] K) := by
    constructor
    intro z hz
    have hr := (TensorProduct.injective_and_range_eq_invariants
      (⊤ : Subgroup (K ≃ₐ[k] K)) hfixed A).2
    have hmem : z ∈ Set.range ((TensorProduct.mk k A K).flip (1 : K)) := by
      rw [hr]
      intro σ
      change map (AlgHom.id k A) (σ : K ≃ₐ[k] K).toAlgHom z = z
      exact hz σ
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha⟩
  have hunder : x.asIdeal.under A = y.asIdeal.under A :=
    congrArg PrimeSpectrum.asIdeal hxy
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := A) (G := K ≃ₐ[k] K) x.asIdeal y.asIdeal hunder
  refine ⟨σ⁻¹, ?_⟩
  apply PrimeSpectrum.ext
  rw [hσ]
  ext z
  change map (AlgHom.id k A) (σ⁻¹).toAlgHom z ∈ x.asIdeal ↔ z ∈ σ • x.asIdeal
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

end Algebra.TensorProduct
