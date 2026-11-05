/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ProperExchangeFinite
public import WeilConjectures.SixFunctors.NearbyCycles.PushforwardExchangeSquare
public import WeilConjectures.SixFunctors.NearbyCycles.StrictlyHenselianTrait
import WeilConjectures.Tactic.ExactModProofs

/-!

# Step (B): global cohomology of nearby cycles under change of strictly henselian trait

Let `ι : R₁ ⟶ R₂` be a local homomorphism of strictly henselian local rings (for instance
strictly henselian discrete valuation rings), with compatible maps `aᵢ : Rᵢ ⟶ Ωᵢ` to separably
closed fields (geometric generic points) and `bᵢ : Rᵢ ⟶ κᵢ` to fields (special points, `b₂` with
kernel the maximal ideal), compatible with `c : Ω₁ ⟶ Ω₂` and `d : κ₁ ⟶ κ₂`. Let `N` be a model
**proper** over `S₁ = Spec R₁` along `q₁`, `M` its base change to `S₂ = Spec R₂` and `φ : M ⟶ N`
the morphism of models. Write `p₂ : X'_{s₂} ⟶ Spec κ₂` for the special fibre of `M`.

Step (B) of the proof of SGA 4½, [Th. finitude], Prop. 3.7: the global cohomology
`Rp₂_*` of the pullback exchange `α : Lf'^* Ψ_N ⟶ Ψ_M Lφ^*` (with coefficients in a finite ring)
is an isomorphism at every complex bounded below of étale origin on the geometric generic fibre
of `N` (`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_isProper_trait`). Both sides
compute the cohomology of the geometric generic fibre:
`RΓ(X_{s₂}, Ψ_M K) = RΓ(X_{η̄₂}, K) = RΓ(X_{η̄₁}, K) = RΓ(X_{s₁}, Ψ_N K)`.

Formally, `φ`, the structure morphisms `N ⟶ S₁`, `M ⟶ S₂` (`NearbyCyclesModel.Hom.toOfTrait`) and
the morphism of traits `S₂ ⟶ S₁` (`NearbyCyclesModel.ofTraitHom`) form a commutative square of
morphisms of models, and the square law of the pushforward exchanges
(`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_square`) applies. Its inputs are
* the proper exchange for `N ⟶ S₁` and `M ⟶ S₂`
  (`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient`);
* proper base change for the square of special fibres and for the square of geometric generic
  fibres `X_{η̄₂} ⟶ X_{η̄₁}`; the latter is the invariance of `RΓ(X_η̄, -)` under the extension
  `Ω₁ ⟶ Ω₂` of separably closed fields
  (`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_finiteCoefficient`);
* the invariance of the nearby cycles of the trait itself
  (`NearbyCyclesModel.isIso_pullbackExchange_ofTraitHom_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]
  {R₁ R₂ : Type u} [CommRing R₁] [IsStrictlyHenselianLocalRing R₁] [CommRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂} [IsLocalHom ι]
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂] [IsSepClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂} {d : κ₁ →+* κ₂}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
