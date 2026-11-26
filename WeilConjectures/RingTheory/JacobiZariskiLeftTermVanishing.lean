/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Vanishing of the left base-change term of the Jacobi-Zariski sequence

If `H₁(L_{B/A}) = 0` and `Ω_{B/A}` is projective, the left base-change term of the
Jacobi–Zariski sequence for `A → B → B/a` vanishes.

## Implementation details

With `M` the range of the naive cotangent differential `δ`, the exact sequences
`0 → H₁ → N₁ → M → 0` and `0 → M → N₀ → Ω_{B/A} → 0` have flat right-hand terms, so they stay
exact after tensoring with `B/a`.

## References

* [Stacks, Tag 00S2]
-/

@[expose] public section

universe u v

open TensorProduct

namespace Algebra

/-- If `H₁(L_{B/A}) = 0` and `Ω_{B/A}` is projective, then for the canonical presentation
`A[B] → B` and an ideal `a`, the tensor of the kernel inclusion with `B ⧸ a` is injective and
identifies its source with the kernel of the tensored differential; both modules vanish. -/
theorem jacobiZariski_leftTerm_vanishing
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Subsingleton (H1Cotangent A B)] [Module.Projective B (KaehlerDifferential A B)]
    (a : Ideal B) :
    let P := (Generators.self A B).toExtension
    let δ := P.cotangentComplex.rTensor (B ⧸ a)
    let ι := P.h1Cotangentι.rTensor (B ⧸ a)
    Function.Injective ι ∧ LinearMap.range ι = LinearMap.ker δ ∧
      Nonempty ((LinearMap.ker δ) ≃ₗ[B] (H1Cotangent A B ⊗[B] (B ⧸ a))) ∧
      Subsingleton (H1Cotangent A B ⊗[B] (B ⧸ a)) ∧
      Subsingleton (LinearMap.ker δ) := by
  let P := (Generators.self A B).toExtension
  -- Zero first homology makes the differential injective before base change.
  have hδ : Function.Injective P.cotangentComplex :=
    P.subsingleton_h1Cotangent.mp inferInstance
  -- Its cokernel is projective, hence flat; apply tensor injectivity directly.
  have hδtensor : Function.Injective (P.cotangentComplex.rTensor (B ⧸ a)) :=
    (P.cotangentComplex.lTensor_inj_iff_rTensor_inj (B ⧸ a)).mp
      (LinearMap.lTensor_injective_of_exact_of_flat P.toKaehler P.toKaehler_surjective
        P.cotangentComplex hδ P.exact_cotangentComplex_toKaehler (B ⧸ a))
  have hker : LinearMap.ker (P.cotangentComplex.rTensor (B ⧸ a)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hδtensor
  let : Subsingleton (LinearMap.ker (P.cotangentComplex.rTensor (B ⧸ a))) :=
    Submodule.subsingleton_iff_eq_bot.mpr hker
  refine ⟨fun _ _ _ ↦ Subsingleton.elim _ _, ?_,
    ⟨LinearEquiv.ofSubsingleton _ _⟩, inferInstance, inferInstance⟩
  rw [hker]
  apply LinearMap.range_eq_bot.mpr
  exact Subsingleton.elim _ _

end Algebra
