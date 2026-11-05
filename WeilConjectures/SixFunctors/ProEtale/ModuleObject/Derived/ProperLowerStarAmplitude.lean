/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum

/-!
# Amplitude of the direct image along an exact change of coefficients

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings whose extensions of scalars
`Λ'_X ⊗_{Λ_X} -` are exact, and `p : Z ⟶ Y` a morphism of schemes such that the (Push)
comparison `Λ'_Y ⊗ᴸ Rp_* K ⟶ Rp_*(Λ'_Z ⊗ᴸ K)` is invertible on bounded below complexes. If `Rp_*`
sends the constructible `Λ_Z`-modules, placed in degree `0`, into degrees `≤ d`, then it sends
into degrees `≤ d` every `Λ'_Z`-module `N` such that `N[0] ≅ Λ'_Z ⊗ᴸ K₀` for a bounded
constructible `Λ_Z`-complex `K₀`
(`ProEtale.CondensedRing.isLE_rightDerivedLowerStar_singleFunctor_of_extendScalars`).

Indeed `Rp_*(N[0]) ≅ Λ'_Y ⊗ Rp_* K₀`. In the truncation triangle
`τ^{< 1} K₀ ⟶ K₀ ⟶ τ^{≥ 1} K₀ ⟶`, the complex `Λ'_Y ⊗ Rp_* τ^{≥ 1} K₀ ≅ Rp_*(Λ'_Z ⊗ τ^{≥ 1} K₀)`
vanishes, `Λ'_Z ⊗ -` commuting with truncations and `N[0]` being concentrated in degree `0`,
while `Rp_* τ^{< 1} K₀` lies in degrees `≤ d` by dévissage
(`DerivedCategory.isLE_obj_of_isLE_of_homologyProperty`).

This is the passage from the integral to the rational coefficients, and from finite
subextensions `E` to `ℚ̄_ℓ`, in the proof of blueprint `det-proper-heart-bound-rational`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme DerivedCategory.TStructure

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ]

variable {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [IsCommMonObj Λ] [MonObj Λ']
  [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

end AlgebraicGeometry.ProEtale.CondensedRing
