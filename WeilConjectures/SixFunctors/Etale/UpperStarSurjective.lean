/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Pullback along a surjective morphism reflects zero objects and monomorphisms

For a surjective morphism of schemes `f : U ⟶ X`, the pullback `f^*` of étale sheaves of
`Λ`-modules is exact and conservative
(`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective`), hence reflects
zero objects and monomorphisms (blueprint `det-tf-transverse-corner-vanishing`, dévissage step).

## Main statements

- `AlgebraicGeometry.Etale.isZero_of_isZero_upperStar_obj`
- `AlgebraicGeometry.Etale.mono_of_mono_upperStar_map`
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {U X : Scheme.{u}} (f : U ⟶ X)
  (hf : Function.Surjective f.base)

include hf in
/-- The pullback along a surjective morphism reflects zero objects
(blueprint `det-tf-transverse-corner-vanishing`). -/
theorem isZero_of_isZero_upperStar_obj {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : IsZero ((f)^*[ModuleCat.{u + 1} Λ].obj F)) : IsZero F := by
  have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (ι := PUnit.{u + 1}) (fun _ ↦ f) (fun x ↦ ⟨⟨⟩, hf x⟩) (0 : F ⟶ 0)
    (fun _ ↦ isIso_of_source_target_iso_zero _ hF.isoZero
      (Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

include hf in
/-- The pullback along a surjective morphism reflects monomorphisms
(blueprint `det-tf-transverse-corner-vanishing`). -/
theorem mono_of_mono_upperStar_map {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (χ : F ⟶ G) [Mono ((f)^*[ModuleCat.{u + 1} Λ].map χ)] : Mono χ :=
  Preadditive.mono_of_kernel_zero ((isZero_of_isZero_upperStar_obj f hf
    ((isZero_kernel_of_mono ((f)^*[ModuleCat.{u + 1} Λ].map χ)).of_iso
      (PreservesKernel.iso _ χ))).eq_of_src _ _)

end AlgebraicGeometry.Etale
