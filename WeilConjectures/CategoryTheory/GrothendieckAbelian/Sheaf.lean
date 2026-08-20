/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!

# The sheaf categories on the small sites are Grothendieck abelian (sorried)

The category of `A`-valued sheaves on the small `Q`-site of `P`-schemes is Grothendieck
abelian, for a Grothendieck abelian category `A` with `Hom`-types in the universe `u` of
the base schemes: the site is essentially small, so the sheaf category is equivalent to
a category of sheaves on a small site, which is Grothendieck abelian.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- The category of `A`-valued sheaves on the small `Q`-site of `P`-schemes over a scheme
`U` is Grothendieck abelian, for a Grothendieck abelian coefficient category `A` with
`Hom`-types in the universe `u` of the base schemes: the site is essentially small for
the étale-like properties `P` of interest, so the sheaf category is equivalent to a
category of sheaves on a small site, which is Grothendieck abelian. -/
instance (priority := high) isGrothendieckAbelian_sheaf_smallGrothendieckTopology (A : Type u')
    [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    IsGrothendieckAbelian.{u} (Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) :=
  sorry

/-- The category of `A`-valued sheaves on the small étale site is Grothendieck abelian:
the instance above specialized to `P = Q = @Etale`. -/
instance (priority := high) isGrothendieckAbelian_sheaf_smallEtaleTopology (A : Type u')
    [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A] (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology A) :=
  inferInstanceAs (IsGrothendieckAbelian.{u}
    (Sheaf (X.smallGrothendieckTopology (P := @Etale) (Q := @Etale)) A))

end CategoryTheory.GrothendieckTopology
