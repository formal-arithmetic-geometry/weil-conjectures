/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme

/-!
# Integrality is insensitive to thickenings

## References

* [Stacks Project, Tag 09ZV](https://stacks.math.columbia.edu/tag/09ZV)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Integrality is invariant under a morphism of arbitrary thickenings. No cartesian
or finite order assumption is needed. -/
theorem isIntegralHom_iff_of_thickenings {S S' X X' : Scheme.{u}}
    (i_S : S ⟶ S') (i_X : X ⟶ X') (f' : X' ⟶ S') (f : X ⟶ S)
    (hS : IsThickening i_S) (hX : IsThickening i_X)
    (hcomm : i_X ≫ f' = f ≫ i_S) : IsIntegralHom f ↔ IsIntegralHom f' := by
  have : IsClosedImmersion i_S := hS.1
  have : IsClosedImmersion i_X := hX.1
  have : Surjective i_X := hX.2
  constructor
  · intro hf
    have : IsIntegralHom f := hf
    have : UniversallyClosed (i_X ≫ f') := by
      rw [hcomm]
      infer_instance
    have : UniversallyClosed f' := UniversallyClosed.of_comp_surjective i_X f'
    have : IsAffineHom f' := by
      constructor
      intro U hU
      have hpre : IsAffineOpen (i_X ⁻¹ᵁ (f' ⁻¹ᵁ U)) := by
        rw [← Scheme.Hom.comp_preimage, hcomm, Scheme.Hom.comp_preimage]
        exact (hU.preimage i_S).preimage f
      have : IsAffine (i_X ⁻¹ᵁ (f' ⁻¹ᵁ U)).toScheme := hpre
      have : Surjective (i_X ∣_ (f' ⁻¹ᵁ U)) := by
        constructor
        intro x
        obtain ⟨y, hy⟩ := i_X.surjective x.1
        refine ⟨⟨y, ?_⟩, ?_⟩
        · change i_X y ∈ f' ⁻¹ᵁ U
          rw [hy]
          exact x.2
        · apply Subtype.ext
          simpa only [morphismRestrict_base_coe] using hy
      exact isAffine_of_isThickening (i_X ∣_ (f' ⁻¹ᵁ U))
        ⟨inferInstance, inferInstance⟩
    exact IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  · intro hf'
    have : IsIntegralHom f' := hf'
    have : IsIntegralHom (f ≫ i_S) := by
      rw [← hcomm]
      infer_instance
    exact IsIntegralHom.of_comp f i_S

end AlgebraicGeometry
