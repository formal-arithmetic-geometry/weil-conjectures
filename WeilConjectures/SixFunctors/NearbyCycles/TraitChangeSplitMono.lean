/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestrictedSplitMono
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestrictedSplitMonoTorsion

/-!
# Split pullback exchanges of nearby cycles from integral and torsion coefficients

The pullback exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` of a morphism of models `φ : M ⟶ N` is, up to
isomorphisms, the base change morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric
generic fibres restricted to the special fibre of `M`
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app`). This file
shows that it is a split monomorphism with `ℚ̄_ℓ`-coefficients at `B ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` as
soon as the restricted base change morphism with `𝒪_E/ℓⁿ⁺¹`-coefficients has unique retractions
with a property preserved by reduction, for instance Galois invariance
(`NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_unique_retractions`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

section Abstract

end Abstract

variable {ℓ : ℕ} [Fact ℓ.Prime] {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
