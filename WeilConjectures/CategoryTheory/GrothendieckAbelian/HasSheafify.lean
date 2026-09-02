/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients

/-!

# Sheafification on the small sites

Sheafification exists for `A`-valued presheaves on the small `Q`-sites of `P`-schemes,
for a coefficient category `A` with `Hom`-types in the universe `u + 1`, one above the
universe `u` of the base schemes, with small-site sheafification
(`CategoryTheory.HasSmallSiteSheafify`): the sites have objects in `Type (u + 1)` and
`Hom`-types in `Type u`, so they are essentially `u + 1`-small, which is what the class
asks sheafification for.

The same applies to the localizations `J.over V` of these sites at an object `V`: a slice
of such a site is again a site of this kind. These localized instances are what lets the
constructible-sheaf definitions of `WeilConjectures.ConstructibleSheaf.Defs` restrict a
sheaf to a member of an étale cover without carrying `HasWeakSheafify` for the localized
sites as a hypothesis.

The instances below are keyed on the small sites rather than obtained from a global instance
`CategoryTheory.HasSmallSiteSheafify.hasSheafify_of_essentiallySmall`, whose conclusion
`HasSheafify J A` would match every sheafification goal in the library and be attempted on
all of them.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Sheafification for `A`-valued presheaves on the small `Q`-site of `P`-schemes over a
scheme `U`, for a coefficient category `A` with small-site sheafification and `Hom`-types in
the universe `u + 1`, one above the universe `u` of the base schemes: the site has objects
in `Type (u + 1)` and `Hom`-types in `Type u`, so it is essentially `u + 1`-small. -/
instance (priority := high) hasSheafify_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [HasSmallSiteSheafify A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    HasSheafify (U.smallGrothendieckTopology Q (Q := P)) A :=
  HasSmallSiteSheafify.hasSheafify_of_essentiallySmall A _

/-- Sheafification for `A`-valued presheaves on the small étale site, the case
`P = Q = @Etale` of the above. -/
instance (priority := high) hasSheafify_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [HasSmallSiteSheafify A] (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology A :=
  inferInstanceAs (HasSheafify (X.smallGrothendieckTopology (P := @Etale) (Q := @Etale)) A)

/-- Sheafification for `A`-valued presheaves on the localization at `V` of the small
`Q`-site of `P`-schemes over `U`, for a coefficient category `A` with small-site
sheafification: the slice of the site at `V` again has objects in `Type (u + 1)` and
`Hom`-types in `Type u`. -/
instance (priority := high) hasSheafify_over_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [HasSmallSiteSheafify A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) (V : P.Over ⊤ U) :
    HasSheafify ((U.smallGrothendieckTopology Q (Q := P)).over V) A :=
  HasSmallSiteSheafify.hasSheafify_of_essentiallySmall A _

/-- Sheafification for `A`-valued presheaves on the localization of the small étale site
at an étale `U ⟶ X`, the case `P = Q = @Etale` of the above. This is what lets a sheaf be
restricted to a member of an étale cover without assuming `HasWeakSheafify` for the
localized site. -/
instance (priority := high) hasSheafify_over_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [HasSmallSiteSheafify A] (X : Scheme.{u}) (U : X.Etale) :
    HasSheafify (X.smallEtaleTopology.over U) A :=
  inferInstanceAs
    (HasSheafify ((X.smallGrothendieckTopology (P := @Etale) (Q := @Etale)).over U) A)

end CategoryTheory.GrothendieckTopology
