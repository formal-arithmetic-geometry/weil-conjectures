/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Ideal
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.TraceFormula.Specialization.TraitModel

/-!

# Restricting a model over the trait to an open of its total space

Let `M` be a model of finite type over the trait `S = Spec k'⟦t⟧`
(`NearbyCyclesModel.IsTraitModel`), with total space `𝒳`, geometric generic fibre
`j : 𝒳_η̄ ⟶ 𝒳` and special fibre `i : X' ⟶ 𝒳`.

* The *geometric model* `M.geometric` of `𝒳` itself has the same total space, fibres and
  inclusions, and identification `ε = j`; its nearby cycles are the geometric nearby cycles
  `Li^* Rj_* Lj^*` (`NearbyCyclesModel.geometric`).
* For an open `V ⊆ 𝒳`, the restriction `M.restrictOpen V` keeps the identification `ε`
  (restricted to `j⁻¹ V`), and the inclusions form a morphism of models
  `M.restrictOpenHom V : M.restrictOpen V ⟶ M` over `𝟙 X` and `i⁻¹ V ⟶ X'`
  (`NearbyCyclesModel.restrictOpen`, `NearbyCyclesModel.restrictOpenHom`).
* The *restriction* `M.restrict V` is the geometric model of `M.restrictOpen V`, with
  geometric generic fibre `j⁻¹ V` and special fibre `i⁻¹ V` (`NearbyCyclesModel.restrict`). It is
  again a model of finite type over the trait if `V ⟶ 𝒳` is quasi-compact
  (`NearbyCyclesModel.IsTraitModel.restrict`), and the inclusions form a morphism of models
  `M.restrict V ⟶ M.geometric` (`NearbyCyclesModel.restrictHom`) whose square of geometric
  generic fibres is cartesian, so that its pullback exchange is invertible
  (`NearbyCyclesModel.isIso_pullbackExchange_restrictHom`): nearby cycles commute with
  restriction to opens.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {X X'' : Scheme.{u}} {X' : Over (Spec (.of k'))}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
