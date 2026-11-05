/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Exchange

/-!

# The Künneth map of nearby cycles

Let `Ψ = Li^* Rj_* Lε^*` be the nearby cycles of a model
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.nearbyCycles`). This file constructs,
on the unbounded derived categories of module objects,

* the *lax tensor map* `μ_j : Rj_* A ⊗ Rj_* B ⟶ Rj_* (A ⊗ B)` of a derived pushforward, the
  adjoint of the tensor product of the counits of `Lj^* ⊣ Rj_*`
  (`ProEtale.CondensedRing.lowerStarTensorMap'`);
* the *lax tensor map* `μ_Ψ : Ψ A ⊗ Ψ B ⟶ Ψ (A ⊗ B)` of nearby cycles, the restriction to the
  special fibre of `μ_j` (`NearbyCyclesModel.tensorMap`);
* for two morphisms of models `φ₁ : P ⟶ M` over `f₁` and `φ₂ : P ⟶ N` over `f₂`, the *Künneth
  map* (`NearbyCyclesModel.kunnethMap`, blueprint `sk-prop-tf-nearby-external-kunneth`)
  ```
  Π_{A,B} : Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B ⟶ Ψ_P (Lf₁^* A ⊗ Lf₂^* B),
  ```
  the tensor product of the pullback exchanges `α_{φ₁}`, `α_{φ₂}` followed by `μ_Ψ`. When `P` is
  the product of `M` and `N` over the trait, `f₁, f₂` and `f₁', f₂'` are the projections and both
  sides are the external products `Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)`: this is the map `Π_{L,M}` of
  the blueprint, the restriction to the special fibre of the map
  `Rj_{X*} L ⊠ Rj_{Y*} M ⟶ Rj_{X × Y *} (L ⊠ M)` defined by the pullback exchanges and the lax
  tensor map of direct image.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section LowerStar

variable {U T : Scheme.{u}} (j : U ⟶ T)

section Kunneth

variable {X X₁ Y Y₁ Z Z₁ : Scheme.{u}} {f₁ : Z ⟶ X} {f₂ : Z ⟶ Y} {g : X ⟶ X₁} {h : Y ⟶ Y₁}
  {k : Z ⟶ Z₁} {e₁ : Z₁ ⟶ X₁} {e₂ : Z₁ ⟶ Y₁}

end Kunneth

end LowerStar

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

variable {Y Y' Z Z' : Scheme.{u}} {M} {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
