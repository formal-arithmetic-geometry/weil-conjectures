/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# The pullback of a constructible sheaf is constructible

For a morphism of schemes `g : X ⟶ Y` and a constructible sheaf `F` on the small étale
site of `Y` (`AlgebraicGeometry.Scheme.IsConstructibleSheaf`), the pullback `g^* F` is
constructible, see [Stacks 03SB]. This is stated here with `sorry`; it is the geometric
input for the fact that the derived pullback preserves the bounded constructible derived
category, see `WeilConjectures.CategoryTheory.DerivedCategory.ConstructiblePullback`.

## Main statements

- `AlgebraicGeometry.Scheme.isConstructibleSheaf_upperStar`: the pullback of a
  constructible étale sheaf is constructible.

-/

@[expose] public section

universe u u'

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The pullback of a constructible étale sheaf along a morphism of schemes `g : X ⟶ Y` is
constructible ([Stacks 03SB]).

Given a stratification of `Y` trivializing `F`, its pullback along `g` is a stratification
of `X`: the base change of an immersion is an immersion and the preimages of the strata
partition `X` into locally closed subsets. On each stratum the restriction of `g^* F` is
the pullback of the restriction of `F`, and the pullback of a finite locally constant
sheaf is finite locally constant, a trivializing cover being pulled back and the stalks
being unchanged. -/
instance isConstructibleSheaf_upperStar (F : Sheaf Y.smallEtaleTopology A)
    [IsConstructibleSheaf F] : IsConstructibleSheaf ((Etale.upperStar A g).obj F) :=
  sorry

end AlgebraicGeometry.Scheme

end
