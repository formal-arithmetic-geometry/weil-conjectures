/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestrictedSplitMono.PadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestrictedSplitMono.PadicSubfield

/-!
# Split restricted base change maps under coefficient change

For a commutative square `sq : g' ≫ p' = p ≫ g` and `i : Z ⟶ Y'`, consider the restricted base
change map `Li^* BC_sq(K) : Li^* Lg^* Rp_* K ⟶ Li^* Rp'_* Lg'^* K`. This file shows that its split
injectivity is compatible with the coefficient changes `𝒪_E/ℓⁿ ⟵ 𝒪_E ⟶ E ⟶ ℚ̄_ℓ`, as
`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_integral` does for its
invertibility:

* `ProEtale.CondensedRing.isSplitMono_map_baseChangeMap_app_padicSubfield_of_padicIntegers` and
  `ProEtale.CondensedRing.isSplitMono_map_baseChangeMap_app_padicAlgCl_of_padicSubfield`: flat
  extension of scalars along `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` carries split monomorphisms to split monomorphisms
  through the arrow isomorphisms
  `ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app_of_flat`;
  `ProEtale.CondensedRing.isSplitMono_map_baseChangeMap_app_of_iso_extendScalars` transports along
  an integral model.

The flat case and the two coefficient changes are proved in the files of the directory
`CoefficientChangeRestrictedSplitMono`; this file proves the transport along an integral model.
The case of `𝒪_E/ℓⁿ⁺¹`-coefficients is in `CoefficientChangeRestrictedSplitMonoTorsion.lean`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Transport

variable {Λ₁ Λ₂ Λ₃ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ₁]
  [IsCommMonObj Λ₁] [MonObj Λ₂] [IsCommMonObj Λ₂] [MonObj Λ₃] [IsCommMonObj Λ₃]
  (a : Λ₁ ⟶ Λ₂) [IsMonHom a] (b : Λ₂ ⟶ Λ₃) [IsMonHom b]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

end Transport

end AlgebraicGeometry.ProEtale.CondensedRing
