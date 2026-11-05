/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite

/-!
# Finiteness of `Rf_*` for `E` and `ℚ̄_ℓ` from the integral case

Let `ℓ` be a prime and `f : X ⟶ Y` a quasi-compact quasi-separated morphism of schemes, with `X`
topologically noetherian. The second paragraph of the proof of blueprint
`lem-sfb-dc-lower-star-preserves` deduces the preservation of bounded constructible complexes by
`Rf_*` for the coefficient rings `E` (a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`) and `ℚ̄_ℓ` from the
one for the rings of integers `𝒪_E`. This file formalizes this deduction:

* `boundedConstructible_rightDerivedLowerStar_obj_continuousMapRingObj_of_padicIntegers`:
  if `Rf_*` preserves `Dᵇc(-)⟦𝒪_E⟧`, it preserves `Dᵇc(-)⟦E⟧`. A bounded constructible
  `E`-complex is `E ⊗ᴸ_{𝒪_E} K₀` for an integral model `K₀`
  (`ProEtale.exists_boundedConstructibleExtendScalars_obj_iso`), the comparison **(Push)**
  `E ⊗ᴸ Rf_* K₀ ⟶ Rf_*(E ⊗ᴸ K₀)` is an isomorphism on bounded below objects
  (`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicIntegers_of_isGE`), and `E ⊗ᴸ -`
  preserves bounded constructible complexes
  (`ProEtale.boundedConstructible_derivedExtendScalars_obj`).
* `boundedConstructible_rightDerivedLowerStar_obj_padicAlgCl_of_continuousMapRingObj`:
  if `Rf_*` preserves `Dᵇc(-)⟦E⟧` for every finite subextension `E`, it preserves
  `Dᵇc(-)⟦ℚ̄_ℓ⟧`. A bounded constructible `ℚ̄_ℓ`-complex descends to some `E`
  (`ProEtale.constructibleCocone_essSurjObj`), the comparison (Push) for `E ⟶ ℚ̄_ℓ` is an
  isomorphism on bounded below objects
  (`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`),
  and `ℚ̄_ℓ ⊗ᴸ_E -` preserves bounded constructible complexes
  (`ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`).
* `boundedConstructible_rightDerivedLowerStar_obj_padicAlgCl_of_padicIntegers`:
  the composite of the two.

## Implementation notes

These statements are made above
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, since the
comparisons (Push) and the integral models are proved in files importing it. They take the
integral finiteness as a hypothesis, so that they do not depend on the `sorry`ed finiteness
theorems of that file.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
  (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

end AlgebraicGeometry.ProEtale.CondensedRing
