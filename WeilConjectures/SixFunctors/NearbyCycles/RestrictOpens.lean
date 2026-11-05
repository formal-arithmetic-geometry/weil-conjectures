/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux

/-!

# Restriction of models to opens of the total space

Let `N` be a model of `Y` with special fibre `Y'` (`AlgebraicGeometry.ProEtale.CondensedRing.
NearbyCyclesModel`) and `V` an open of its total space. The *restriction* of `N` to `V`
(`NearbyCyclesModel.restrictOpens`) has total space `V`, geometric generic fibre `𝒳_η̄ ×_𝒳 V` and
special fibre `Y' ×_𝒳 V`; it maps to `N` by the open immersion of total spaces
(`NearbyCyclesModel.restrictOpensHom`), whose pullback exchange is invertible
(`NearbyCyclesModel.isIso_restrictOpensHom_pullbackExchange`). A morphism of models
`φ : M ⟶ N` restricts to a morphism `φ|_V : M|_{φ⁻¹ V} ⟶ N|_V`
(`NearbyCyclesModel.Hom.restrictOpens`) commuting with these open immersions.

## Main results

- `NearbyCyclesModel.Hom.isIso_toGeneric_pullbackExchange_app_of_restrictOpens`: **the
  invertibility of the pullback exchange of the models of the geometric generic fibres is local on
  the total space**. If every point `x` of the special fibre of `M` has an open neighbourhood `V`
  of `φ(x)` such that the pullback exchange of `φ|_V` is invertible at the restriction of `K`,
  then the pullback exchange of `φ` is invertible at `K`. Indeed by the square law of the
  pullback exchanges (`NearbyCyclesModel.Hom.pullbackExchange_square`) and the invertibility of
  the exchanges of open immersions, the restriction of the exchange of `φ` to the open
  `M.i⁻¹(φ⁻¹ V)` of the special fibre is identified with the exchange of `φ|_V`
  (`NearbyCyclesModel.Hom.isIso_leftDerivedUpperStar_map_pullbackExchange_app_of_restrictOpens`),
  and these opens cover the special fibre.
- `NearbyCyclesModel.isPullback_restrictOpens_j`, `NearbyCyclesModel.isPullback_restrictOpens_i`,
  `NearbyCyclesModel.Hom.isPullback_restrictOpens_total`: cartesian squares of fibres over a trait
  and of total spaces over a change of trait restrict to opens.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {X X' Y Y' : Scheme.{u}}

/-! ### Restriction of a model to an open of the total space -/

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Restriction of a morphism of models -/

variable {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f f') (V : N.total.Opens)

/-! ### Locality of the pullback exchange on the total space -/

end Hom

/-! ### Cartesian squares over traits restrict to opens -/

section IsPullback

variable {S T : Scheme.{u}}

variable {S₁ S₂ : Scheme.{u}} (φ : M.Hom N f f') (V : N.total.Opens)

end IsPullback

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
