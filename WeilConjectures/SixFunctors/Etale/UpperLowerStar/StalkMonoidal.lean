/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!

# Stalks of étale sheaves of modules commute with the tensor product

Let `Λ` be a commutative ring and `s : Spec Ω ⟶ X` a geometric point of a scheme `X`. The
stalk functor at `s` on étale sheaves of `Λ`-modules is strong monoidal: the stalk of a
tensor product of sheaves is the tensor product of the stalks, `(F ⊗ G)_s ≅ F_s ⊗ G_s`,
naturally in `F` and `G`, and the stalk of the unit sheaf is `Λ`.

The site-general input is Mathlib's monoidal instance on
`CategoryTheory.GrothendieckTopology.Point.sheafFiber` (in
`Mathlib.CategoryTheory.Sites.Point.Monoidal`): the presheaf fibre is a filtered colimit, the
tensor product of `Λ`-modules commutes with filtered colimits in each variable, and the fibre
of the sheafification of a presheaf is the presheaf fibre. That instance applies to the
universe-lifted point `(pointSmallEtale s).ulift`, the form of the stalk used with
`AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso`.

## Main results

- `AlgebraicGeometry.Etale.sheafFiberTensorIso`: `(F ⊗ G)_s ≅ F_s ⊗ G_s`.
- `AlgebraicGeometry.Etale.sheafFiberUnitIso`: `(𝟙_)_s ≅ 𝟙_`.

## Implementation notes

The monoidal structure on `Sheaf X.smallEtaleTopology (ModuleCat Λ)` is
`CategoryTheory.Sheaf.monoidalCategory`, a local instance in Mathlib; it is activated here by
`attribute [local instance]`, and has to be activated in the same way by users of this file.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Sheaf.monoidalCategory

variable (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

namespace Etale

/-- The stalk of a tensor product of étale sheaves of `Λ`-modules at a geometric point `s`
is the tensor product of the stalks: `(F ⊗ G)_s ≅ F_s ⊗ G_s`. This is the inverse of the
tensorator of the monoidal functor `CategoryTheory.GrothendieckTopology.Point.sheafFiber`. -/
noncomputable def sheafFiberTensorIso (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((pointSmallEtale s).ulift.{u + 1}).sheafFiber.obj (F ⊗ G) ≅
      ((pointSmallEtale s).ulift.{u + 1}).sheafFiber.obj F ⊗
        ((pointSmallEtale s).ulift.{u + 1}).sheafFiber.obj G :=
  (Functor.Monoidal.μIso _ F G).symm

@[reassoc]
lemma sheafFiberTensorIso_hom_naturality
    {F F' G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ F') (g : G ⟶ G') :
    ((pointSmallEtale s).ulift.{u + 1}).sheafFiber.map (f ⊗ₘ g) ≫
        (sheafFiberTensorIso Λ s F' G').hom =
      (sheafFiberTensorIso Λ s F G).hom ≫
        (((pointSmallEtale s).ulift.{u + 1}).sheafFiber.map f ⊗ₘ
          ((pointSmallEtale s).ulift.{u + 1}).sheafFiber.map g) :=
  (Functor.OplaxMonoidal.δ_natural _ f g).symm

/-- The stalk of the unit étale sheaf of `Λ`-modules at a geometric point is `Λ`, the unit
of `ModuleCat Λ`. -/
noncomputable def sheafFiberUnitIso :
    ((pointSmallEtale s).ulift.{u + 1}).sheafFiber.obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) ≅
      𝟙_ (ModuleCat.{u + 1} Λ) :=
  (Functor.Monoidal.εIso _).symm

end Etale

end AlgebraicGeometry
