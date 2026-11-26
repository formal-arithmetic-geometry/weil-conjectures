/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness over a base ring survives algebra-module localization

If `M` is an `A`-module flat over `R`, then every localization `S⁻¹M` is flat over `R`.

## Implementation details

For an injective map of `R`-modules `N₁ → N₂`, the map `M ⊗[R] N₁ → M ⊗[R] N₂` is injective and
`A`-linear; localizing at `S` preserves injectivity, and the localization-tensor identification
turns it into `S⁻¹M ⊗[R] N₁ → S⁻¹M ⊗[R] N₂`.

## References

* [Stacks, Tag 00HT]
-/

@[expose] public section

namespace Module.Flat

/-- Let `R → A` be a map of commutative rings, `M` an `A`-module flat over `R`, and `S` a
submonoid of `A`. Then `S⁻¹M`, regarded as an `R`-module through `A → S⁻¹A`, is flat over
`R`. -/
theorem localizedModule_of_algebra {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] (S : Submonoid A) (hM : Module.Flat R M) :
    Module.Flat R (LocalizedModule S M) := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  let g : M →ₗ[A] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  have hinj : Function.Injective (LinearMap.lTensor M N.subtype) :=
    hM.lTensor_preserves_injective_linearMap N.subtype N.subtype_injective
  have hinjA : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) := by
    simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using hinj
  have hloc := IsLocalizedModule.map_injective S
    (TensorProduct.AlgebraTensorModule.rTensor R N g)
    (TensorProduct.AlgebraTensorModule.rTensor R P g)
    (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) hinjA
  rw [IsLocalizedModule.map_lTensor] at hloc
  simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using hloc

end Module.Flat
