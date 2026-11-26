/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimesFlatBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Associated primes of a quotient under flat base change

For a flat map of Noetherian rings `R → S` and an ideal `I` of `R`, every associated prime of
`S/IS` is an associated prime of `S/pS` for some associated prime `p` of `R/I`.

## Implementation details

This applies `RingTheory.annihilatorAssociatedPrimes_flat_base_change` with `M = R/I` and
`N = S`, identifying `(R/I) ⊗_R S` with `S/IS` by right exactness of the tensor product.
The cases `I = ⊤` and `I = ⊥` need no separate argument.

## References

* [Stacks, Tag 0312]
* [Stacks, Tag 0330]
-/

@[expose] public section

universe u v

open scoped TensorProduct Pointwise

/-- For a flat map of Noetherian rings `R → S` and an ideal `I` of `R`, every associated prime of
`S/IS` is an associated prime of `S/pS` for some associated prime `p` of `R/I`. -/
theorem associatedPrimes_quotient_map_of_flat
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (I : Ideal R) (q : Ideal S)
    (hq : q ∈ associatedPrimes S (S ⧸ I.map (algebraMap R S))) :
    ∃ p ∈ associatedPrimes R (R ⧸ I),
      q ∈ associatedPrimes S (S ⧸ p.map (algebraMap R S)) := by
  let : Module S ((R ⧸ I) ⊗[R] S) :=
    (TensorProduct.comm R (R ⧸ I) S).toAddEquiv.module S
  let e : ((R ⧸ I) ⊗[R] S) ≃ₗ[S] (S ⧸ I.map (algebraMap R S)) :=
    (TensorProduct.comm R (R ⧸ I) S).toAddEquiv.linearEquiv S ≪≫ₗ
      (Ideal.quotMapEquivTensorQuot S).symm
  have hqt : q ∈ RingTheory.annihilatorAssociatedPrimes S ((R ⧸ I) ⊗[R] S) := by
    exact isAssociatedPrime_iff.mp ((e.isAssociatedPrime_iff).mpr hq)
  have hf := (RingTheory.annihilatorAssociatedPrimes_flat_base_change (R := R) (S := S)
    (R ⧸ I) S).2 (inferInstance : IsNoetherianRing R)
  rw [hf] at hqt
  obtain ⟨p, hp, hqp⟩ := Set.mem_iUnion₂.mp hqt
  have hp' : p ∈ associatedPrimes R (R ⧸ I) := isAssociatedPrime_iff.mpr hp
  have heq : (p : Set R) • (⊤ : Submodule S S) = p.map (algebraMap R S) := by
    apply le_antisymm
    · apply Submodule.set_smul_le
      intro r n hr hn
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr)
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      have h := Submodule.mem_set_smul_of_mem_mem (N := (⊤ : Submodule S S)) hr
        (show (1 : S) ∈ (⊤ : Submodule S S) from trivial)
      simpa [Algebra.smul_def] using h
  refine ⟨p, hp', ?_⟩
  rw [heq] at hqp
  exact isAssociatedPrime_iff.mpr hqp
