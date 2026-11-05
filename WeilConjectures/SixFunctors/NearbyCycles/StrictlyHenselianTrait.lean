/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.StrictlyHenselianBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar
import WeilConjectures.Tactic.ExactModProofs

/-!

# Nearby cycles of a strictly henselian trait

Let `R` be a ring with a map `a : R ⟶ Ω` (a geometric generic point when `R` is a strictly
henselian trait and `Ω` an algebraically closed extension of its fraction field) and a map
`b : R ⟶ κ` (a special point). The spectrum `S = Spec R` is a model of `Spec Ω` with special
fibre `Spec κ` and identification `ε = 𝟙` (`NearbyCyclesModel.ofTrait`), whose nearby cycles are
`Li^* Ra_*`. A model `N` lying over `S` maps to it (`NearbyCyclesModel.Hom.toOfTrait`), and a
morphism of traits `S₂ ⟶ S₁` compatible with the points is a morphism of models
(`NearbyCyclesModel.ofTraitHom`).

**Invariance of the nearby cycles of the trait itself under change of trait.** If `ι : R₁ ⟶ R₂`
is a local homomorphism of strictly henselian local rings, `Ωᵢ` are separably closed and `b₂` has
kernel the maximal ideal, the pullback exchange `Ld^* Ψ_{S₁} ⟶ Ψ_{S₂} Lc^*` of the morphism of
traits is invertible at every complex bounded below of étale origin, with coefficients in a finite
ring `T` (`NearbyCyclesModel.isIso_pullbackExchange_ofTraitHom_app`). This is the trait case of
SGA 4½, [Th. finitude], Prop. 3.7, and the input to its step (B): both sides compute the
cohomology of the geometric generic point. It follows from
`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_of_isStrictlyHenselianLocalRing`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

section Defs

variable {R Ω κ : Type u} [CommRing R] [CommRing Ω] [CommRing κ]

variable {R₁ R₂ Ω₁ Ω₂ κ₁ κ₂ : Type u} [CommRing R₁] [CommRing R₂] [CommRing Ω₁] [CommRing Ω₂]
  [CommRing κ₁] [CommRing κ₂]

end Defs

section Exchange

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]
  {R₁ R₂ : Type u} [CommRing R₁] [IsStrictlyHenselianLocalRing R₁] [CommRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂]
  [IsSepClosed Ω₂] {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂]

end Exchange

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
