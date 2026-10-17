/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Etale.Basic

/-!
# Integral closure commutes with étale base change

Let `B` be a ring, `L` a `B`-algebra with integral closure `T = integralClosure B L`, and
`B → B₁` a smooth (e.g. étale) ring map. Then the canonical map `B₁ ⊗[B] T → B₁ ⊗[B] L` is
injective and its image is the integral closure of `B₁` in `B₁ ⊗[B] L`.

This is a reformulation of Mathlib's `TensorProduct.toIntegralClosure_bijective_of_smooth`
(which is proved by reducing to the standard étale case and the trace/dual basis argument),
in the form used in the trait case of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`), where `B → B₁` is an étale base change adjoining roots
of unity.

## Main results

- `TensorProduct.map_integralClosure_val_injective`: the map `B₁ ⊗[B] T → B₁ ⊗[B] L` is
  injective for flat `B₁`.
- `TensorProduct.range_map_integralClosure_val`: its image is `integralClosure B₁ (B₁ ⊗[B] L)`
  for smooth (in particular étale) `B₁`.
- `TensorProduct.integralClosureEquivOfSmooth`: the resulting isomorphism
  `B₁ ⊗[B] integralClosure B L ≃ₐ[B₁] integralClosure B₁ (B₁ ⊗[B] L)`.
-/

@[expose] public section

open TensorProduct

namespace TensorProduct

variable {B B₁ L : Type*} [CommRing B] [CommRing B₁] [Algebra B B₁] [CommRing L] [Algebra B L]

/-- For a flat `B`-algebra `B₁`, the map `B₁ ⊗[B] integralClosure B L → B₁ ⊗[B] L` is
injective. -/
theorem map_integralClosure_val_injective [Module.Flat B B₁] :
    Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id B₁ B₁) (integralClosure B L).val) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := B₁)
    (integralClosure B L).val.toLinearMap Subtype.val_injective

/-- **Integral closure commutes with smooth (e.g. étale) base change.** For a smooth
`B`-algebra `B₁`, the image of `B₁ ⊗[B] integralClosure B L → B₁ ⊗[B] L` is the integral closure
of `B₁` in `B₁ ⊗[B] L`. Used in the trait case of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`). -/
theorem range_map_integralClosure_val [Algebra.Smooth B B₁] :
    (Algebra.TensorProduct.map (AlgHom.id B₁ B₁) (integralClosure B L).val).range =
      (integralClosure B₁ (B₁ ⊗[B] L)) := by
  have hbij := toIntegralClosure_bijective_of_smooth (R := B) (S := B₁) (B := L)
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    exact (toIntegralClosure B B₁ L y).2
  · obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

/-- **Integral closure commutes with smooth (e.g. étale) base change**, as an isomorphism
`B₁ ⊗[B] integralClosure B L ≃ₐ[B₁] integralClosure B₁ (B₁ ⊗[B] L)`. -/
noncomputable def integralClosureEquivOfSmooth (B₁ L : Type*) [CommRing B₁] [Algebra B B₁]
    [CommRing L] [Algebra B L] [Algebra.Smooth B B₁] :
    B₁ ⊗[B] integralClosure B L ≃ₐ[B₁] integralClosure B₁ (B₁ ⊗[B] L) :=
  AlgEquiv.ofBijective (toIntegralClosure B B₁ L) toIntegralClosure_bijective_of_smooth

@[simp]
lemma integralClosureEquivOfSmooth_tmul [Algebra.Smooth B B₁] (b : B₁)
    (t : integralClosure B L) :
    (integralClosureEquivOfSmooth B₁ L (b ⊗ₜ t) : B₁ ⊗[B] L) = b ⊗ₜ (t : L) :=
  rfl

end TensorProduct
