/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.CompletionMapBijective

/-!
# Flat local maps induce isomorphisms on adic completions

A flat local homomorphism of Noetherian local rings inducing an isomorphism on residue fields
induces an isomorphism on adic completions.

## Implementation details

The completion of `B` is finite and flat, hence free, over the completion of `A`; comparing
fibres at the residue field shows the rank is one, so the completed map is bijective.

## References

* [Stacks, Tag 0AGX]
-/

@[expose] public section

universe u v

namespace RingHom

/--
A flat local homomorphism of Noetherian local rings inducing an isomorphism on
residue fields induces an isomorphism on the corresponding adic completions.
-/
theorem flat_local_completion_iso
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) (hflat : φ.Flat) [IsLocalHom φ]
    (hmax : Ideal.map φ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B)
    (hres : Function.Bijective (Ideal.quotientMap (IsLocalRing.maximalIdeal B) φ
      (IsLocalRing.maximalIdeal_comap φ).ge)) :
    ∃ (φhat : AdicCompletion (IsLocalRing.maximalIdeal A) A →+*
        AdicCompletion (IsLocalRing.maximalIdeal B) B),
      (∀ (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) (a : A),
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n) a →
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal B) n (φhat x) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal B ^ n) (φ a)) ∧
      Function.Bijective φhat ∧
        φhat.comp (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) =
          (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp φ := by
  obtain ⟨φhat, heval, hcomp, hflat⟩ :=
    flat_adicCompletion_of_flat_local A B φ hflat (fun x hx => map_nonunit φ x hx)
  have hbij := completion_map_bijective φ hmax hres φhat hcomp hflat
  refine ⟨φhat, ?_, hbij, hcomp⟩
  intro n x a hx
  have hx' := congrArg (fun f => f x) (heval n)
  dsimp at hx'
  rw [hx] at hx'
  exact hx'

end RingHom
