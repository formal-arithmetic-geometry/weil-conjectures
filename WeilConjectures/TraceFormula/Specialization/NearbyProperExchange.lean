/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ProperExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperNoetherianBase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.NearbySpecialFibreBaseChange
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The proper exchange of nearby cycles

For a morphism `φ : M ⟶ N` of nearby cycles models of finite type over the trait
`S = Spec k'⟦t⟧` over a proper `f` whose morphism of total spaces is proper and whose squares of
special fibres and of identifications `ε` are cartesian, the pushforward exchange
`χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` (`NearbyCyclesModel.Hom.pushforwardExchange`) is an isomorphism on
bounded constructible `ℚ̄_ℓ`-complexes (blueprint `det-sp-nearby-cycles-exchanges` (2), "proper
exchange", `NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`), provided the
target `Y` of `f` is noetherian over a field in which `ℓ` is invertible. For the geometric models,
whose identifications are the inclusions of the geometric generic fibres, this is
`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_geometric`.

Following the proof of the blueprint, `χ_f` is the composite of `Li_N^* Rj_{N*}` of the base
change morphism of the square of identifications, of the comparison of the two generic direct
images, and of the base change morphism of the square of special fibres at `Rj_{M*} Lε_M^* K`
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isIso_baseChangeMap`). The first is
invertible by proper base change over noetherian bases mapping to fields
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`), the
last by proper base change at generic direct images
(`NearbyCyclesModel.Hom.isIso_baseChangeMap_commSq_i_app_lowerStar`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [Fact (ringChar k' ≠ ℓ)]

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
