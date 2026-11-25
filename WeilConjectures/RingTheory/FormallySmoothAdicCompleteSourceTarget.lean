/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.CompletionMapForLocalHom
import WeilConjectures.RingTheory.FormallySmoothAdicCompletionTransfer

/-!
# Adic formal smoothness after completing source and target

A local map of Noetherian local rings induces a map of maximal-ideal completions, and formal
smoothness for the target's maximal-ideal-adic topology passes to this map.

## Implementation details

Completion of the target preserves adic formal smoothness over the original source
(Tag 07ED, (1) implies (2)). For a lifting problem over the completed source, the lift
obtained over the original source kills a power of the extended target ideal (Tag 07EC), and
since every element of the completed source is congruent to an original-source element
modulo any power of its maximal ideal (Tag 05GG), the lift is linear over the completed
source.

## References

* [Stacks, Tag 07ED], (1) implies (3)
* [Stacks, Tag 07EC]
* [Stacks, Tag 05GG]
-/

@[expose] public section

universe u v

namespace Algebra

/-- A local map of Noetherian local rings induces a map between their maximal-ideal
completions, specified on every quotient coordinate. Formal smoothness for the target's
maximal-ideal adic topology passes to this map, with the extended target ideal. -/
theorem exists_formallySmoothAdic_completeSourceTarget
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ] :
    ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal A) A →+*
        AdicCompletion (IsLocalRing.maximalIdeal B) B,
      (∀ (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) (a : A),
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n x =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a →
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal B) n (ψ x) =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B) ^ n) (φ a)) ∧
      (letI := φ.toAlgebra
       FormallySmoothAdic A B (IsLocalRing.maximalIdeal B) →
         letI := ψ.toAlgebra
         FormallySmoothAdic (AdicCompletion (IsLocalRing.maximalIdeal A) A)
           (AdicCompletion (IsLocalRing.maximalIdeal B) B)
           ((IsLocalRing.maximalIdeal B).map
             (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)))) := by
  obtain ⟨ψ, hψ⟩ := RingHom.exists_adicCompletion_map_of_local φ
  refine ⟨ψ, hψ, ?_⟩
  exact formallySmoothAdic_completion_transfer A B φ ψ hψ

end Algebra
