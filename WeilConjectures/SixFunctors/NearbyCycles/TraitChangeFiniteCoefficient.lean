/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChange
public import WeilConjectures.Tactic.ExactModProofs
public import WeilConjectures.Tactic.TransportExact

/-!

# Invariance of nearby cycles under change of trait, finite coefficients

The pullback exchange form of Deligne's theorem (SGA 4½, [Th. finitude], Prop. 3.7) with
coefficients a finite discrete ring `T` in which the residual characteristic is invertible
(`ProEtale.CondensedRing.isIso_pullbackExchange_app_of_isPullback_trait_finite`): for a change of
strictly henselian traits the pullback exchange `α : Lf'^* Ψ_N B ⟶ Ψ_M (Lf^* B)` is invertible
at every `B` whose restriction to the geometric generic fibre of `N` is bounded below of étale
origin. It is `NearbyCyclesModel.traitChangeInvariance` after replacing the special fibre of `N`
by its fibre over the residue field of the target trait, which does not change the base change
morphism of `Rj_*` on the special fibre of `M`
`NearbyCyclesModel.Hom.isIso_map_exchangeRight_app_of_isIso_pullbackExchange_toGenericWithSpecial`.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]
  {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂}
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ : Type u} [Field κ] [IsSepClosed κ] {b₂ : R₂ →+* κ}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

end AlgebraicGeometry.ProEtale.CondensedRing
