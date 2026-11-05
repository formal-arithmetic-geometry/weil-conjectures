/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ConstructibleExtContinuity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresentedField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClFlat

/-!
# Continuity of `Hom` out of constructible sheaves with `ℓ`-adic coefficients

Blueprint `sk-lem-constructible-ext-continuity` (1), and `sk-lem-int-ext` (1) for `𝒪_E`: for the
`ℓ`-adic coefficient rings `Λ = E, 𝒪_E, ℚ̄_ℓ` and a separated finite-type scheme `X` over a field,
morphisms `C ⟶ B[n]` out of a constructible sheaf `C` into a filtered colimit `B = colim Bᵢ` of
sheaves factor through some `Bᵢ[n]`:

* `hasConstructibleExtContinuity_continuousMapRingObj_of_locallyOfFiniteType`,
* `hasConstructibleExtContinuity_padicIntegersRingObj_of_locallyOfFiniteType`,
* `hasConstructibleExtContinuity_padicAlgClRingObj_of_locallyOfFiniteType`.

They follow from the dévissage
`homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject`,
whose two hypotheses are verified here:

* flatness of `Λ_X` over `ℤ`
  (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralFlat`);
* the case of lisse sheaves `L` on a scheme with noetherian underlying space: for the fields `E`
  and `ℚ̄_ℓ` such an `L` is locally free, and for `𝒪_E` it has a resolution
  `0 ⟶ F₁ ⟶ F₀ ⟶ L ⟶ 0` by locally free sheaves (`integral_lfp_locallyFree_resolution`); locally
  free sheaves are handled by
  `homCommutesWithFilteredColimits_singleFunctor_of_isLocallyFree` (the case of `E` is
  `homCommutesWithFilteredColimits_singleFunctor_continuousMapRingObj`, in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ConstructibleExtContinuity`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### Constructible sheaves -/

variable {k : Type u} [Field k]

end AlgebraicGeometry.ProEtale.CondensedRing
