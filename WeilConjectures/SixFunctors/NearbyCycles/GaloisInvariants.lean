/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisAction
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerAction

/-!

# Nearby cycles of an intermediate field as invariants: the formal part

Let `N` be a model of `X` with special fibre `X'`, `h : N.generic ⟶ Spec L`, `Ω/L` a field
extension, `N_Ω` the Galois layer (`NearbyCyclesModel.galoisLayer`) with generic fibre
`G_Ω = N.generic ×_{Spec L} Spec Ω` and projection `g : G_Ω ⟶ N.generic`. The pullback exchange
`α : L(𝟙)^* Ψ_N C ⟶ Ψ_{N_Ω} (L(𝟙)^* C)` of the projection `N_Ω ⟶ N` is `Li^* Rj_*` of the derived
unit `A ⟶ Rg_* Lg^* A` at `A = Lε^* C`
(`NearbyCyclesModel.Hom.pullbackExchange_app_of_total_eq_id`),
and the action of `σ ∈ Aut(Ω/L)` on `Ψ_{N_Ω}` is `Li^* Rj_*` of the derived unit transport `u_σ`
along `Spec σ` (`NearbyCyclesModel.galoisLayerAut_autAction`).

Hence a retraction `R` of the derived unit which is invariant under all the `u_σ` gives a
retraction `r` of `α` whose idempotent `r ≫ α` is fixed by the action of `Aut(Ω/L)` on both sides
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_invariant`): `α` is the
inclusion of a direct summand of `Ψ_{N_Ω}`, cut out by a Galois-invariant projector onto the
invariant part. This is the formal part of the identification `Ψ_N = (Ψ_{N_Ω})^P` (SGA 4½,
[Th. finitude], Lemme 3.4; blueprint `sk-prop-tf-nearby-external-kunneth`, identification (2)).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
