/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!

# The sheaf categories on the small sites are Grothendieck abelian

The category of `A`-valued sheaves on the small `Q`-site of `P`-schemes is Grothendieck
abelian, for a Grothendieck abelian category `A` with small-site sheafification
(`CategoryTheory.HasSmallSiteSheafify`) and `Hom`-types in the universe `u + 1`, one above
the universe `u` of the base schemes: the site has objects in `Type (u + 1)` and
`Hom`-types in `Type u`, so it is essentially `u + 1`-small, and the sheaf category is
equivalent to a category of sheaves on a small site, which is Grothendieck abelian
(`CategoryTheory.Sheaf.isGrothendieckAbelian_of_hasSmallSiteSheafify`). Since the site has
`Hom`-types in `u`, the sheaf category again has `Hom`-types in `u + 1`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- The category of `A`-valued sheaves on the small `Q`-site of `P`-schemes over a scheme
`U` is Grothendieck abelian, for a Grothendieck abelian coefficient category `A` with small
site coefficients and `Hom`-types in the universe `u + 1`, one above the universe `u` of
the base schemes: the site is essentially `u + 1`-small, so the sheaf category is
equivalent to a category of sheaves on a small site, which is Grothendieck abelian. -/
instance isGrothendieckAbelian_sheaf_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [HasSmallSiteSheafify A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) :=
  Sheaf.isGrothendieckAbelian_of_hasSmallSiteSheafify A _

/-- The category of `A`-valued sheaves on the small étale site is Grothendieck abelian:
the instance above specialized to `P = Q = @Etale`. -/
instance isGrothendieckAbelian_sheaf_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [HasSmallSiteSheafify A] (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology A) :=
  inferInstanceAs (IsGrothendieckAbelian.{u + 1}
    (Sheaf (X.smallGrothendieckTopology (P := @Etale) (Q := @Etale)) A))

/-- The category of `A`-valued sheaves on the localization at `V` of the small `Q`-site of
`P`-schemes over `U` is Grothendieck abelian: the slice of the site at `V` is again
essentially `u + 1`-small. -/
instance isGrothendieckAbelian_sheaf_over_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [HasSmallSiteSheafify A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) (V : P.Over ⊤ U) :
    IsGrothendieckAbelian.{u + 1} (Sheaf ((U.smallGrothendieckTopology Q (Q := P)).over V) A) :=
  Sheaf.isGrothendieckAbelian_of_hasSmallSiteSheafify A _

end CategoryTheory.GrothendieckTopology
