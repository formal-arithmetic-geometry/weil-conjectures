/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariants
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.FieldTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar

/-!

# Nearby cycles of an intermediate field are the invariants, torsion coefficients

Let `N` be a model of `X` with special fibre `X'`, `h : N.generic ⟶ Spec L`, `Ω/L` a Galois
extension (possibly infinite) whose finite Galois subextensions have degrees invertible in a finite
discrete commutative ring `T₀` (for instance `Ω/L` pro-`p` and `T₀ = 𝒪_E/ϖⁿ` with `p ≠ ℓ`), and
`Λ = C(-, T₀)`. For `C ∈ D(Mod_{Λ_X})` whose restriction to the generic fibre is bounded below of
étale origin, the pullback exchange `α : Ψ_N C ⟶ Ψ_{N_Ω} C` of the projection from the Galois layer
`N_Ω` (generic fibre `N.generic ×_L Ω`) is a split monomorphism, with a retraction whose idempotent
is fixed by the action of `Gal(Ω/L)` on both sides
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin`): `α` is
the inclusion of the `Gal(Ω/L)`-invariant direct summand of `Ψ_{N_Ω} C`.

For a model over a strictly henselian trait whose generic fibre lies over the generic point
`η = Spec L` and `Ω` the separable closure of `L`, the group `Gal(Ω/L)` is the inertia group `I`,
and for a closed subgroup `P ⊆ I` with fixed field `L_P = Ω^P`, `N_{L_P}` is the model with generic
fibre over `L_P`; applied to `Ω/L_P` this gives `Ψ_{N_{L_P}} = (Ψ_{N_Ω})^P` (SGA 4½, [Th. finitude],
Lemme 3.4; blueprint `sk-prop-tf-nearby-external-kunneth`, identification (2)), for pro-`p` `P`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]
  {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
