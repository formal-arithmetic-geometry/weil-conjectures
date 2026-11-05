/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperNoetherianBase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicIntegers

/-!
# Proper base change and the projection formula for `E`-sheaves

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ`. This file deduces proper base change and the
proper projection formula for bounded constructible `E`-complexes from the integral statements
(blueprint `det-thm-sfb-proper-base-change-rational` (3), for `Λ = E`):

* `ProEtale.CondensedRing.isIso_baseChangeMap_app_padicSubfield_of_isProper`: for a cartesian
  square `g' ≫ p = p' ≫ g` with `p` proper over noetherian bases over fields in which `ℓ` is
  invertible, the base change map with coefficients `E` is invertible at every bounded
  constructible `E`-complex;
* `ProEtale.CondensedRing.isIso_projectionMap_continuousMapRingObj_of_boundedConstructible`: for
  a proper `p`, the projection map with coefficients `E` is invertible at bounded constructible
  `E`-complexes.

A bounded constructible `E`-complex `K` has an integral model: `K ≅ E ⊗ᴸ_{𝒪_E} K₀` for a bounded
constructible `𝒪_E`-complex `K₀`
(`ProEtale.CondensedRing.exists_derivedExtendScalars_iso_integralModel`),
and the extension of scalars `𝒪_E ⟶ E` is flat and commutes with the direct images of bounded
below complexes, so both statements are transported from `𝒪_E` to `E`
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicSubfield_of_padicIntegers`,
`ProEtale.CondensedRing.isIso_projectionMap_app_app_padicSubfield_of_padicIntegers`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

end AlgebraicGeometry.ProEtale.CondensedRing
