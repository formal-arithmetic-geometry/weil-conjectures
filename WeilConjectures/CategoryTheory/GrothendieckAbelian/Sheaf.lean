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
the base schemes.

As for sheafification, the input is *not* essential smallness of the site — the small
sites are not essentially small, see the module docstring of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify` — but the essentially
small dense affine subsite of `Mathlib.AlgebraicGeometry.Sites.Affine`. Along the
resulting equivalence of sheaf categories one transports mathlib's
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`, exactly as
`AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology` does for a
concrete coefficient category.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- The category of `A`-valued sheaves on the small `Q`-site of `P`-schemes over a scheme
`U` is Grothendieck abelian, for a Grothendieck abelian coefficient category `A` with
`Hom`-types in the universe `u` of the base schemes: the affine slice of the site is an
essentially small dense subsite, so the sheaf category is equivalent to a category of
sheaves on an essentially small site, which is Grothendieck abelian. -/
instance (priority := high) isGrothendieckAbelian_sheaf_smallGrothendieckTopology (A : Type u')
    [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    [IsZariskiLocalAtSource P]
    (U : Scheme.{u})
    [EssentiallySmall.{u} (MorphismProperty.CostructuredArrow P ⊤ Scheme.Spec U)] :
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
