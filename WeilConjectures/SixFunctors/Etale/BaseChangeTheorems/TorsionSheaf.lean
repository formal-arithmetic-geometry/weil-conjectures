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

Let `Λ` be a commutative ring and `X` a scheme. This file defines the two
torsion conditions entering the statement of the proper base change theorem:

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

Torsion refers throughout to the underlying abelian group, not to the `Λ`-module
structure: for `Λ = ℤ` the definition specializes to torsion abelian sheaves, the
setting of the classical proper base change theorem [Stacks 0DDE], and for a coefficient
ring `Λ` which is torsion as an additive group — in particular for the finite rings
`Λ = ℤ/ℓⁿℤ` of the `ℓ`-adic formalism — every sheaf of `Λ`-modules is torsion
(`AlgebraicGeometry.Scheme.IsTorsionSheaf.of_isTorsion`).

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

end AlgebraicGeometry
