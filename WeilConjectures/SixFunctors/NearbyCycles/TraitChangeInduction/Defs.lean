/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar

/-!

# The statement of Deligne's induction for the change of strictly henselian trait

Let `T` be a finite discrete ring. `NearbyCyclesModel.TraitChangeInvariance T m` is the statement
of SGA 4½, [Th. finitude], Prop. 3.7, with coefficients `T`, for models whose total space locally
embeds into `𝔸ᵐ` over the base (`AlgebraicGeometry.Scheme.Hom.LocallyEmbedsInAffineSpace`): for
an unramified local injection `ι : R₁ ⟶ R₂` of strictly henselian discrete valuation rings, with
compatible algebraic geometric generic points `Spec Ω₂ ⟶ Spec Ω₁` and residual characteristic
exponent invertible in `T`, a model `N` separated of finite type over `S₁ = Spec R₁` and its base
change `M` to `S₂ = Spec R₂`, both special fibres over the same separably closed field `κ`, the
pullback exchange `Lf'^* Ψ_N K ⟶ Ψ_M (Lφ^* K)` of the models of the geometric generic fibres
(`NearbyCyclesModel.Hom.toGeneric`) is invertible at every complex `K` bounded below of étale
origin.

It is proved by induction on `m` in
`WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Basic`.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
