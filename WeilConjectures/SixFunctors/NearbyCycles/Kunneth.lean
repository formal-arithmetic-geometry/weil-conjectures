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

/-- The *lax tensor map* `μ_j : Rj_* A ⊗ Rj_* B ⟶ Rj_* (A ⊗ B)` of the derived pushforward on
module objects: the adjoint for `Lj^* ⊣ Rj_*` of
```
Lj^* (Rj_* A ⊗ Rj_* B) ≅ Lj^* Rj_* A ⊗ Lj^* Rj_* B --ε ⊗ ε--> A ⊗ B,
```
the monoidal structure of `Lj^*` followed by the counits. -/
noncomputable def lowerStarTensorMap'
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    R((j)_*⟦Λ⟧).obj A ⊗ R((j)_*⟦Λ⟧).obj B ⟶ R((j)_*⟦Λ⟧).obj (A ⊗ B) :=
  (derivedUpperStarLowerStarAdjunction Λ j).homEquiv _ _
    (Functor.OplaxMonoidal.δ L((j)^*⟦Λ⟧) _ _ ≫
      ((derivedUpperStarLowerStarAdjunction Λ j).counit.app A ⊗ₘ
        (derivedUpperStarLowerStarAdjunction Λ j).counit.app B))

end LowerStar

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

/-- The *lax tensor map* `μ_Ψ : Ψ A ⊗ Ψ B ⟶ Ψ (A ⊗ B)` of the nearby cycles `Ψ = Li^* Rj_* Lε^*`:
the monoidal structure of `Li^*`, then `Li^*` of the lax tensor map `μ_j` of `Rj_*`, and finally
`Li^* Rj_*` of the monoidal structure of `Lε^*`. -/
noncomputable def tensorMap
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (M.nearbyCycles Λ).obj A ⊗ (M.nearbyCycles Λ).obj B ⟶ (M.nearbyCycles Λ).obj (A ⊗ B) :=
  Functor.LaxMonoidal.μ L((M.i)^*⟦Λ⟧) _ _ ≫
    L((M.i)^*⟦Λ⟧).map (lowerStarTensorMap' Λ M.j _ _ ≫
      R((M.j)_*⟦Λ⟧).map (Functor.LaxMonoidal.μ L((M.ε)^*⟦Λ⟧) A B))

variable {Y Y' Z Z' : Scheme.{u}} {M} {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

/-- The **Künneth map of nearby cycles** (blueprint `sk-prop-tf-nearby-external-kunneth`, the map
`Π_{L,M}`): for morphisms of models `φ₁ : P ⟶ M` over `f₁, f₁'` and `φ₂ : P ⟶ N` over `f₂, f₂'`,
```
Π_{A,B} : Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B ⟶ Ψ_P (Lf₁^* A) ⊗ Ψ_P (Lf₂^* B) ⟶ Ψ_P (Lf₁^* A ⊗ Lf₂^* B),
```
the tensor product of the pullback exchanges `α_{φ₁}(A)` and `α_{φ₂}(B)` followed by the lax
tensor map `μ_Ψ` of `Ψ_P`. For the product `P` of `M` and `N` over the trait, with the
projections, it is the map `Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)`. -/
noncomputable def kunnethMap (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    L((f₁')^*⟦Λ⟧).obj ((M.nearbyCycles Λ).obj A) ⊗ L((f₂')^*⟦Λ⟧).obj ((N.nearbyCycles Λ).obj B) ⟶
      (P.nearbyCycles Λ).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) :=
  ((φ₁.pullbackExchange Λ).app A ⊗ₘ (φ₂.pullbackExchange Λ).app B) ≫ P.tensorMap Λ _ _

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
