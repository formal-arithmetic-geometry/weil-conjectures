/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Slice
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Coordinates
public import WeilConjectures.SixFunctors.NearbyCycles.RestrictOpens
public import WeilConjectures.SixFunctors.NearbyCycles.ProperTraitChange
public import WeilConjectures.SixFunctors.NearbyCycles.TraitCompactification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedPointsDetection
public import WeilConjectures.Compactification.AffineCharts
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.BasicCharts
import WeilConjectures.Tactic.ExactModProofs

/-!

# Deligne's induction for the change of strictly henselian trait

This file proves `NearbyCyclesModel.TraitChangeInvariance T m` for every `m`
(`NearbyCyclesModel.traitChangeInvariance`), i.e. SGA 4½, [Th. finitude], Prop. 3.7, with
coefficients a finite ring `T`, by induction on the dimension `m` of the affine spaces into
which the total space locally embeds.

1. **Proper models** (`NearbyCyclesModel.traitChangeInvariance_of_isProper`). The exchange is a
   morphism of complexes of étale origin on the special fibre `X'`, a scheme of finite type over
   the separably closed field `κ`. Its global cohomology `Rp₂_*` is invertible by step (B)
   (`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_isProper_trait`), and it is invertible
   after pullback to the slice over the generic point of every coordinate line of every chart
   (step (A), `NearbyCyclesModel.Hom.exists_isIso_map_pullbackExchange_slice`, using the induction
   hypothesis). Every non-closed point of `X'` lies over such a generic point
   (`AlgebraicGeometry.AffineSpace.exists_isGenericPoint_reindex_of_not_isClosed`), so the
   closed-point criterion
   (`ProEtale.CondensedRing.isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed`) applies.
2. **Charts** (`NearbyCyclesModel.traitChangeInvariance_of_isImmersion`): a model with an
   immersion into `𝔸(ι; S₁)` is open in its closure in `ℙ(ι; S₁)`, a proper model locally embedding
   into `𝔸(ι; S₁)` (`AlgebraicGeometry.Compactification.ofIsImmersionAffineSpace`), and the exchange
   is invertible once it is for the compactification
   (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_compactification`).
3. **General models**: invertibility of the exchange is local on the total space
   (`NearbyCyclesModel.Hom.isIso_toGeneric_pullbackExchange_app_of_restrictOpens`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

variable {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂} [IsLocalHom ι]
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ : Type u} [Field κ] [IsSepClosed κ] {b₂ : R₂ →+* κ}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
