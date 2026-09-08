/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize

/-!

# Torsion étale sheaves and torsion cohomology

Let `Λ` be a commutative ring and `X` a scheme. This file defines the torsion conditions
entering the statements of the base change theorems:

- `AlgebraicGeometry.Scheme.IsTorsionSheaf`: a sheaf `F` of `Λ`-modules on the small
  étale site of `X` is *torsion* if the stalk of `F` at every geometric point of `X` is
  a torsion abelian group. A geometric point `Spec Ω ⟶ X`, with `Ω` a separably closed
  field, induces a point of the small étale site (`Scheme.pointSmallEtale`), and the
  stalk of `F` is its fiber `CategoryTheory.GrothendieckTopology.Point.sheafFiber` at
  this point. Since the geometric points form a conservative family, this stalkwise
  condition agrees with the classical definition [Stacks 03SA] that `F` is the filtered
  union of its `n`-torsion subsheaves.
- `AlgebraicGeometry.Etale.DerivedCategory.Plus.torsionHomology`: the property of an
  object of the bounded below derived category of étale sheaves of `Λ`-modules that all
  its cohomology sheaves are torsion.

These two are what the proper base change theorem
(`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`) asks of its coefficient
complex. Smooth base change
(`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Smooth`) asks more — it is false
for torsion that is not invertible on the base — and the refinements it needs are defined
here too, relative to a morphism `f : X ⟶ Y`, `Y` being the base of the cartesian square
along which the base change is taken:

- `AlgebraicGeometry.Scheme.OrderInvertibleOn`: `F` is torsion and, at every geometric
  point of `X`, the additive order of every element of the stalk is invertible in the
  ring `Γ(Y, 𝒪_Y)` of global sections of the target of `f`;
- `AlgebraicGeometry.Etale.DerivedCategory.Plus.orderInvertibleOn`: the same asked of
  every cohomology sheaf of an object of the bounded below derived category.

Torsion refers throughout to the underlying abelian group, not to the `Λ`-module
structure: for `Λ = ℤ` the definition specializes to torsion abelian sheaves, the
setting of the classical proper base change theorem [Stacks 0DDE], and for a coefficient
ring `Λ` which is torsion as an additive group — in particular for the finite rings
`Λ = ℤ/ℓⁿℤ` of the `ℓ`-adic formalism — every sheaf of `Λ`-modules is torsion
(`AlgebraicGeometry.Scheme.IsTorsionSheaf.of_isTorsion`). Every torsion order occurring
in a `Λ`-module divides the characteristic of `Λ`, so for such a `Λ` every sheaf is
moreover order invertible on `f` as soon as `ringChar Λ` is a unit of `Γ(Y, 𝒪_Y)`
(`AlgebraicGeometry.Scheme.OrderInvertibleOn.of_isUnit_ringChar`); for `Λ = ℤ/ℓⁿℤ` that
condition says that `ℓ` is invertible on `Y`.

The design follows `AlgebraicGeometry.Scheme.IsFiniteSheaf` of
`WeilConjectures.ConstructibleSheaf.Defs` (stalkwise condition at geometric points) and
`AlgebraicGeometry.Etale.DerivedCategory.constructibleHomology` of
`WeilConjectures.DerivedCategory.Constructible` (homologywise `ObjectProperty` on a
derived category).

Following the convention of the `SixFunctors` folder, the coefficient category has
`Hom`-types in the universe `u + 1`, one above the universe `u` of the base schemes: it
is `ModuleCat.{u + 1} Λ` for a commutative ring `Λ : Type (u + 1)`, mathlib insisting
that the ring and the modules live in the same universe. The `Type u`-valued geometric
points of the small étale site nevertheless have fibers in `ModuleCat.{u + 1} Λ`, the
`u`-indexed filtered colimits computing them being obtained by shrinking from the
`u + 1`-indexed ones, see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize`.

-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

section TorsionSheaf

/-- A sheaf `F` of `Λ`-modules on the small étale site of `X` is *torsion* if the stalk
of `F` at every geometric point of `X` is a torsion abelian group, i.e. every element of
every geometric stalk is killed by a positive integer. Torsion refers to the underlying
abelian group of the stalk, not to its `Λ`-module structure; for `Λ = ℤ` this is the
classical notion of a torsion abelian sheaf [Stacks 03SA]. -/
class Scheme.IsTorsionSheaf {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop where
  isTorsion_sheafFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsAddTorsion (↥((pointSmallEtale s).sheafFiber.obj F))

/-- If the coefficient ring `Λ` is torsion as an additive group — in particular if `Λ`
is finite, e.g. `Λ = ℤ/ℓⁿℤ` — then every sheaf of `Λ`-modules on the small étale site is
torsion: every stalk is a `Λ`-module, and is killed elementwise by the additive order of
`1 : Λ`. -/
lemma Scheme.IsTorsionSheaf.of_isTorsion {Λ : Type (u + 1)} [CommRing Λ]
    (hΛ : IsAddTorsion Λ) {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionSheaf F where
  isTorsion_sheafFiber _ _ _ _ := IsAddTorsion.module_of_torsion Λ _ hΛ

/-- Every sheaf of modules over a finite coefficient ring is torsion. -/
instance {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : IsTorsionSheaf F :=
  .of_isTorsion isAddTorsion_of_finite F

end TorsionSheaf

section OrderInvertibleOn

/-- Let `f : X ⟶ Y` be a morphism of schemes — in the application, the right vertical
arrow of the cartesian square along which the base change is taken, so that `Y` is the
base of the square. A sheaf `F` of `Λ`-modules on the small étale site of `X` is *of
orders invertible on `f`* if it is torsion
(`AlgebraicGeometry.Scheme.IsTorsionSheaf`) and, at every geometric point of `X`, the
additive order of every element of the stalk is invertible in the ring `Γ(Y, 𝒪_Y)` of
global sections of `Y`.

This is the hypothesis on the coefficient sheaf in the smooth base change theorem
[Stacks 0EYU], which is false without it: already for `Y` of characteristic `p` and
`p`-torsion coefficients, by Artin–Schreier.

The torsion condition is asked for separately rather than read off the invertibility: for
a non-torsion element `x` one has `addOrderOf x = 0`, and `IsUnit (0 : Γ(Y, 𝒪_Y))` says
only that the global sections of `Y` form the zero ring. -/
class Scheme.OrderInvertibleOn {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (f : X ⟶ Y) : Prop
    extends IsTorsionSheaf F where
  isUnit_addOrderOf_sheafFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (x : ↥((pointSmallEtale s).sheafFiber.obj F)) :
    IsUnit ((addOrderOf x : ℕ) : Γ(Y, ⊤))

/-- If the coefficient ring `Λ` is torsion as an additive group and its characteristic is
invertible in the global sections of the target of `f` — for `Λ = ℤ/ℓⁿℤ` this says that
`ℓ` is invertible on `Y` — then every sheaf of `Λ`-modules on the small étale site of `X`
is of orders invertible on `f`: every geometric stalk is a `Λ`-module, so the additive
order of each of its elements divides `ringChar Λ`, and a divisor of a unit is a unit. -/
lemma Scheme.OrderInvertibleOn.of_isUnit_ringChar {Λ : Type (u + 1)} [CommRing Λ]
    (hΛ : IsAddTorsion Λ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit ((ringChar Λ : ℕ) : Γ(Y, ⊤)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    OrderInvertibleOn F f where
  __ := IsTorsionSheaf.of_isTorsion hΛ F
  isUnit_addOrderOf_sheafFiber _ _ _ _ x := by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast (addOrderOf_dvd_of_nsmul_eq_zero ?_)) hY
    rw [← Nat.cast_smul_eq_nsmul Λ, ringChar.Nat.cast_ringChar, zero_smul]

end OrderInvertibleOn

section TorsionHomology

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
  [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]

/-- An object of the bounded below derived category of étale sheaves of `Λ`-modules has
*torsion cohomology* if all its cohomology sheaves are torsion
(`AlgebraicGeometry.Scheme.IsTorsionSheaf`). This is the hypothesis on the coefficient
complex in the general proper base change theorem. -/
noncomputable def Etale.DerivedCategory.Plus.torsionHomology :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∀ n : ℤ, IsTorsionSheaf
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).obj K)

/-- If the coefficient ring `Λ` is torsion as an additive group — in particular if `Λ`
is finite — then every object of the bounded below derived category of étale sheaves of
`Λ`-modules has torsion cohomology. -/
lemma Etale.DerivedCategory.Plus.torsionHomology_of_isTorsion (hΛ : IsAddTorsion Λ)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.DerivedCategory.Plus.torsionHomology Λ X K :=
  fun _ ↦ .of_isTorsion hΛ _

end TorsionHomology

section OrderInvertibleHomology

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]

/-- An object of the bounded below derived category of étale sheaves of `Λ`-modules on `X`
has *cohomology of orders invertible on `f`* if all its cohomology sheaves are
(`AlgebraicGeometry.Scheme.OrderInvertibleOn`). This is the hypothesis on the coefficient
complex in the general smooth base change theorem; it refines the
`AlgebraicGeometry.Etale.DerivedCategory.Plus.torsionHomology` of proper base change. -/
noncomputable def Etale.DerivedCategory.Plus.orderInvertibleOn :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∀ n : ℤ, OrderInvertibleOn
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).obj K) f

/-- Cohomology of orders invertible on `f` is in particular torsion cohomology, so the
hypothesis of the smooth base change theorem is stronger than that of the proper base
change theorem. -/
lemma Etale.DerivedCategory.Plus.torsionHomology_of_orderInvertibleOn
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.Plus.orderInvertibleOn Λ f K) :
    Etale.DerivedCategory.Plus.torsionHomology Λ X K :=
  fun n ↦ (hK n).toIsTorsionSheaf

/-- If the coefficient ring `Λ` is torsion as an additive group and its characteristic is
invertible in the global sections of the target of `f`, then every object of the bounded
below derived category of étale sheaves of `Λ`-modules has cohomology of orders invertible
on `f`. -/
lemma Etale.DerivedCategory.Plus.orderInvertibleOn_of_isUnit_ringChar (hΛ : IsAddTorsion Λ)
    (hY : IsUnit ((ringChar Λ : ℕ) : Γ(Y, ⊤)))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.DerivedCategory.Plus.orderInvertibleOn Λ f K :=
  fun _ ↦ .of_isUnit_ringChar hΛ f hY _

end OrderInvertibleHomology

end AlgebraicGeometry
