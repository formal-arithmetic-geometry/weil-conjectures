/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flat maps between completions of Noetherian local rings

Let `φ : A → B` be a homomorphism of Noetherian local rings with `φ(𝔪_A) B = 𝔪_B` inducing a
surjection on residue fields. Then any flat ring homomorphism `Â → B̂` between the
maximal-adic completions which is compatible with `φ` is bijective (Stacks, proof of
Lemma 0AGX).

## Main results

- `RingHom.completion_map_bijective`
-/

@[expose] public section

open IsLocalRing

namespace RingHom

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsNoetherianRing A] [IsNoetherianRing B]

/-- Let `φ : A → B` be a ring homomorphism of Noetherian local rings with `φ(𝔪_A) B = 𝔪_B`
which induces a surjection (e.g. a bijection) of residue fields. Then every flat ring
homomorphism `ψ : Â → B̂` of the maximal-adic completions with `ψ ∘ c_A = c_B ∘ φ` is bijective.
(blueprint: `lem-weil-pbc-flat-local-completion-iso-bijective`) -/
theorem completion_map_bijective (φ : A →+* B) [IsLocalHom φ]
    (hmax : (maximalIdeal A).map φ = maximalIdeal B)
    (hres : Function.Surjective (ResidueField.map φ))
    (ψ : AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B)
    (hψ : ψ.Flat)
    (hcomp : ψ.comp (algebraMap A _) = (algebraMap B _).comp φ) :
    Function.Bijective ψ := by
  have hmax' : (maximalIdeal (AdicCompletion (maximalIdeal A) A)).map ψ =
      maximalIdeal (AdicCompletion (maximalIdeal B) B) := by
    rw [AdicCompletion.maximalIdeal_eq_map, AdicCompletion.maximalIdeal_eq_map, Ideal.map_map,
      hcomp, ← Ideal.map_map, hmax]
  have hloc : IsLocalHom ψ := by
    apply ((IsLocalRing.local_hom_TFAE ψ).out 0 2).mpr
    exact hmax'.le
  let := ψ.toAlgebra
  have : Module.Flat (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) :=
    hψ
  have : IsLocalHom (algebraMap (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B)) := hloc
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := AdicCompletion (maximalIdeal A) A)
    (B := AdicCompletion (maximalIdeal B) B)
  refine ⟨FaithfulSMul.algebraMap_injective (AdicCompletion (maximalIdeal A) A)
    (AdicCompletion (maximalIdeal B) B), ?_⟩
  have : IsHausdorff ((maximalIdeal (AdicCompletion (maximalIdeal A) A)).map ψ)
      (AdicCompletion (maximalIdeal B) B) := by
    rw [hmax']
    infer_instance
  apply surjective_of_mk_map_comp_surjective
    (I := maximalIdeal (AdicCompletion (maximalIdeal A) A))
  intro s'
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
  obtain ⟨y, hy⟩ := (AdicCompletion.residueField_map_bijective B).2 (residue _ s)
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨a', ha'⟩ := hres (residue B b)
  obtain ⟨a, rfl⟩ := residue_surjective a'
  rw [ResidueField.map_residue] at ha' hy
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ at ha' hy
  have ha := Ideal.Quotient.eq.mp ha'
  have hb := Ideal.Quotient.eq.mp hy
  have h1 : ψ (algebraMap A _ a) = algebraMap B (AdicCompletion (maximalIdeal B) B) (φ a) := by
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply]
  refine ⟨algebraMap A _ a, ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq, hmax', h1]
  have he : algebraMap B (AdicCompletion (maximalIdeal B) B) (φ a) - s =
      algebraMap B _ (φ a - b) + (algebraMap B _ b - s) := by
    rw [map_sub]; ring
  rw [he]
  refine add_mem ?_ hb
  exact (map_mem_nonunits_iff (algebraMap B (AdicCompletion (maximalIdeal B) B)) _).mpr ha

end RingHom
