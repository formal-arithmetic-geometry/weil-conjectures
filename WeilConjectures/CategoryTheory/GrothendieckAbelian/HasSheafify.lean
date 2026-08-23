/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!

# Sheafification on the small sites (sorried)

Sheafification exists for `A`-valued presheaves on the small `Q`-sites of `P`-schemes,
for a Grothendieck abelian category `A` with `Hom`-types in the universe `u + 1`, one
above the universe `u` of the base schemes: the sites are essentially small and `A` is
complete and cocomplete with exact filtered colimits of size `u + 1`, so the
plus-construction applies and is left exact.

The same applies to the localizations `J.over V` of these sites at an object `V`: a slice
of an essentially small category is again essentially small. These localized instances are
what lets the constructible-sheaf definitions of
`WeilConjectures.ConstructibleSheaf.Defs` restrict a sheaf to a member of an étale cover
without carrying `HasWeakSheafify` for the localized sites as a hypothesis.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Sheafification for `A`-valued presheaves on the small `Q`-site of `P`-schemes over a
scheme `U`, for a Grothendieck abelian coefficient category `A` with `Hom`-types in the
universe `u + 1`, one above the universe `u` of the base schemes: the site is essentially
small for the étale-like properties `P` of interest and `A` is complete and cocomplete
with exact filtered colimits of size `u + 1`, so the plus-construction applies and is left
exact. -/
instance (priority := high) hasSheafify_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    HasSheafify (U.smallGrothendieckTopology Q (Q := P)) A :=
  sorry

/-- Sheafification for `A`-valued presheaves on the small étale site: the instance above
specialized to `P = Q = @Etale`. -/
instance (priority := high) hasSheafify_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology A :=
  inferInstanceAs (HasSheafify (X.smallGrothendieckTopology (P := @Etale) (Q := @Etale)) A)

/-- Sheafification for `A`-valued presheaves on the localization at `V` of the small
`Q`-site of `P`-schemes over `U`: the site is essentially small for the étale-like
properties `P` of interest, hence so is its slice at `V`, and `A` is complete and
cocomplete with exact filtered colimits of size `u + 1`, so the plus-construction applies
and is left exact. -/
instance (priority := high) hasSheafify_over_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) (V : P.Over ⊤ U) :
    HasSheafify ((U.smallGrothendieckTopology Q (Q := P)).over V) A :=
  sorry

/-- Sheafification for `A`-valued presheaves on the localization of the small étale site
at an étale `U ⟶ X`: the instance above specialized to `P = Q = @Etale`. This is what
lets a sheaf be restricted to a member of an étale cover without assuming
`HasWeakSheafify` for the localized site. -/
instance (priority := high) hasSheafify_over_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u})
    (U : X.Etale) :
    HasSheafify (X.smallEtaleTopology.over U) A :=
  inferInstanceAs (HasSheafify
    ((X.smallGrothendieckTopology (P := @Etale) (Q := @Etale)).over U) A)

end CategoryTheory.GrothendieckTopology
