/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!

# The duality map of nearby cycles

Let `Ψ : C ⥤ C'` be a functor between monoidal closed categories with a lax tensor map
`μ_{A,B} : Ψ A ⊗ Ψ B ⟶ Ψ (A ⊗ B)` (natural in `A` and `B`), and let `θ : Ψ ω ⟶ ω'` be a morphism
from the image of an object `ω` of `C` to an object `ω'` of `C'`. Write `D = RHom(-, ω)` and
`D' = RHom(-, ω')`. The *duality map* (blueprint `sk-prop-tf-nearby-duality-foundation`)
```
δ_M : Ψ D M ⟶ D' Ψ M
```
(`CategoryTheory.Verdier.nearbyDualityMap`) is the tensor–Hom adjoint of the pairing
```
Ψ M ⊗ Ψ D M --μ--> Ψ (M ⊗ D M) --Ψ ev--> Ψ ω --θ--> ω'.
```
In the application `Ψ = S_X = RΨ_{X/S}` is the nearby cycles functor of a scheme `X` over a
strictly henselian trait, `ω`, `ω'` are the dualizing complexes of the generic and special
fibres and `θ = θ_X = β_{a_X}(A)` is the dualizing map of the exceptional exchange; Gabber's
theorem says that `δ_M` is an isomorphism.

The construction is formal, and so are its compatibilities with the operations (blueprint
`det-tf-nearby-duality-proper`), which only use the defining properties of the exchange maps:

* the same construction applied to a lax monoidal functor `G` with a trace `G ω_X ⟶ ω_Y` gives
  the map `G D_X ⟶ D_Y G` of Verdier duality for a proper direct image `G = Rf_*` (with the
  trace `Rf_* ω_X = Rf_! Rf^! ω_Y ⟶ ω_Y`), and the comparison `F D_X ⟶ D_U F` of the duality
  functors for an open restriction `F = j^*` (with `j^* ω_X ≅ ω_U`);
* **proper direct image** (`CategoryTheory.Verdier.nearbyDualityMap_proper`, part (1)): if the
  lax tensor maps commute with the proper exchange `χ : Ψ_Y G ⟶ G' Ψ_X` and the dualizing maps
  satisfy `θ_Y ∘ Ψ_Y(tr) = tr' ∘ G'(θ_X) ∘ χ` (the ordinary-adjoint form of
  `θ_X = f_s^! θ_Y ∘ β_f(ω_Y)`), then `δ_{Y, G M}` and `G' δ_{X,M}` agree under `χ` and the
  Verdier duality maps of `G` and `G'`;
* **open restriction** (`CategoryTheory.Verdier.nearbyDualityMap_restrict`, part (2)): the same
  for a pullback exchange `α : F' Ψ_X ⟶ Ψ_U F` which is monoidal and compatible with `θ`;
* **normalization** (part (3)): on the trait itself nearby cycles are the identity, and the
  duality map with `μ = 𝟙`, `θ = 𝟙` is the identity
  (`CategoryTheory.Verdier.nearbyDualityMap_id`). Combined with part (1) for the structure map
  of a proper scheme this gives that `RΓ(X_s, δ_{X,M})` is an isomorphism as soon as the
  exchange maps and the global Verdier duality maps are
  (`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper`).

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory MonoidalCategory MonoidalClosed

namespace CategoryTheory.Verdier

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
  {C' : Type u₂} [Category.{v₂} C'] [MonoidalCategory C'] [MonoidalClosed C']

section Definition

variable {Ψ : C ⥤ C'} (μ : ∀ A B : C, Ψ.obj A ⊗ Ψ.obj B ⟶ Ψ.obj (A ⊗ B)) {ω : C} {ω' : C'}
  (θ : Ψ.obj ω ⟶ ω')

/-- The pairing `Ψ M ⊗ Ψ D M ⟶ Ψ (M ⊗ D M) ⟶ Ψ ω ⟶ ω'`, `D = RHom(-, ω)`: the lax tensor map,
`Ψ` of the evaluation, and `θ`. -/
noncomputable def nearbyDualityPairing (M : C) : Ψ.obj M ⊗ Ψ.obj ((ihom M).obj ω) ⟶ ω' :=
  μ _ _ ≫ Ψ.map ((ihom.ev M).app ω) ≫ θ

/-- The **duality map** `δ_M : Ψ D M ⟶ D' Ψ M` (blueprint
`sk-prop-tf-nearby-duality-foundation`), `D = RHom(-, ω)` and `D' = RHom(-, ω')`: the tensor–Hom
adjoint of the pairing `θ ∘ Ψ(ev) ∘ μ : Ψ M ⊗ Ψ D M ⟶ ω'`. -/
noncomputable def nearbyDualityMap (M : C) :
    Ψ.obj ((ihom M).obj ω) ⟶ (ihom (Ψ.obj M)).obj ω' :=
  curry (nearbyDualityPairing μ θ M)

lemma uncurry_nearbyDualityMap (M : C) :
    uncurry (nearbyDualityMap μ θ M) = μ _ _ ≫ Ψ.map ((ihom.ev M).app ω) ≫ θ :=
  uncurry_curry _

/-- The duality map composed with the evaluation is the defining pairing. -/
@[reassoc]
lemma whiskerLeft_nearbyDualityMap_comp_ev (M : C) :
    Ψ.obj M ◁ nearbyDualityMap μ θ M ≫ (ihom.ev (Ψ.obj M)).app ω' =
      μ _ _ ≫ Ψ.map ((ihom.ev M).app ω) ≫ θ :=
  whiskerLeft_curry_ihom_ev_app _ _ _

/-- Precomposition with a map `f : ω'₁ ⟶ ω'₂` of the target dualizing objects. -/
lemma nearbyDualityMap_comp_ihom_map {ω'₂ : C'} (f : ω' ⟶ ω'₂) (M : C) :
    nearbyDualityMap μ θ M ≫ (ihom (Ψ.obj M)).map f = nearbyDualityMap μ (θ ≫ f) M := by
  rw [nearbyDualityMap, ← curry_natural_right, nearbyDualityMap, nearbyDualityPairing,
    nearbyDualityPairing, Category.assoc, Category.assoc]

end Definition

/-! ### Normalization -/

section Normalization

/-- **Normalization** (blueprint `det-tf-nearby-duality-proper` (3)): for the identity functor,
with the identity as lax tensor map and as dualizing map, the duality map is the identity. -/
@[simp]
theorem nearbyDualityMap_id (ω : C) (M : C) :
    nearbyDualityMap (Ψ := 𝟭 C) (fun A B ↦ 𝟙 (A ⊗ B)) (𝟙 ω) M = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_nearbyDualityMap]
  change 𝟙 _ ≫ (ihom.ev M).app ω ≫ 𝟙 ω = uncurry (𝟙 ((ihom M).obj ω))
  erw [Category.id_comp, Category.comp_id, uncurry_id_eq_ev]

end Normalization

/-! ### Proper direct image -/

section Proper

variable {D : Type u₃} [Category.{v₃} D] [MonoidalCategory D] [MonoidalClosed D]
  {D' : Type u₄} [Category.{v₄} D'] [MonoidalCategory D'] [MonoidalClosed D']
  {ΨX : C ⥤ C'} {ΨY : D ⥤ D'} (μX : ∀ A B : C, ΨX.obj A ⊗ ΨX.obj B ⟶ ΨX.obj (A ⊗ B))
  (μY : ∀ A B : D, ΨY.obj A ⊗ ΨY.obj B ⟶ ΨY.obj (A ⊗ B))
  {ωX : C} {ωX' : C'} {ωY : D} {ωY' : D'} (θX : ΨX.obj ωX ⟶ ωX') (θY : ΨY.obj ωY ⟶ ωY')
  {G : C ⥤ D} {G' : C' ⥤ D'} [G.LaxMonoidal] [G'.LaxMonoidal]
  (tr : G.obj ωX ⟶ ωY) (tr' : G'.obj ωX' ⟶ ωY')
  (χ : ∀ A : C, ΨY.obj (G.obj A) ⟶ G'.obj (ΨX.obj A))

end Proper

/-! ### Open restriction -/

section Restriction

variable {U : Type u₃} [Category.{v₃} U] [MonoidalCategory U] [MonoidalClosed U]
  {U' : Type u₄} [Category.{v₄} U'] [MonoidalCategory U'] [MonoidalClosed U']
  {ΨX : C ⥤ C'} {ΨU : U ⥤ U'} (μX : ∀ A B : C, ΨX.obj A ⊗ ΨX.obj B ⟶ ΨX.obj (A ⊗ B))
  (μU : ∀ A B : U, ΨU.obj A ⊗ ΨU.obj B ⟶ ΨU.obj (A ⊗ B))
  {ωX : C} {ωX' : C'} {ωU : U} {ωU' : U'} (θX : ΨX.obj ωX ⟶ ωX') (θU : ΨU.obj ωU ⟶ ωU')
  {F : C ⥤ U} {F' : C' ⥤ U'} [F.LaxMonoidal] [F'.LaxMonoidal]
  (ρ : F.obj ωX ⟶ ωU) (ρ' : F'.obj ωX' ⟶ ωU')
  (α : ∀ A : C, F'.obj (ΨX.obj A) ⟶ ΨU.obj (F.obj A))

end Restriction

end CategoryTheory.Verdier
