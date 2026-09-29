/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact

/-!

# Sheafification on essentially small sites (one sorry)

Sheafification exists for `A`-valued presheaves on any essentially small site, for a
Grothendieck abelian category `A` with `Hom`-types in the universe `u + 1`, one above the
universe `u` of the base schemes: the site is equivalent to a small one, and `A` is
complete and cocomplete with exact filtered colimits of size `u + 1`.

The whole file is deduced from the single statement
`CategoryTheory.GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian`, which is the
only sorry: sheafification of `A`-valued presheaves on a *small* site `(C, J)`, for `A`
Grothendieck abelian with `Hom`-types in the universe of `C`. Everything else is proved:
the reduction of an essentially small site to a small one
(`hasSheafify_of_essentiallySmall`), and the fact that the small étale site, the small
pro-étale site and their localizations `J.over V` are essentially small in `u + 1`.

The localized instances are what lets the constructible-sheaf definitions of
`WeilConjectures.ConstructibleSheaf.Defs` restrict a sheaf to a member of an étale cover
without carrying `HasWeakSheafify` for the localized sites as a hypothesis.

## The remaining gap

What is missing is the construction of the reflector, not its exactness: left exactness of
the plus construction over a category with exact filtered colimits is proved, without any
concreteness assumption, in `WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact`
(`CategoryTheory.GrothendieckTopology.preservesFiniteLimits_plusFunctor'`). What is not
available is the sheaf condition: Mathlib's proof that `(P⁺)⁺` is a sheaf
(`Mathlib/CategoryTheory/Sites/ConcreteSheafification.lean`) argues on elements, and for a
target that is merely Grothendieck abelian the two-step plus construction is not known to
suffice. A section of `(P⁺)⁺` over each member of a cover is a section over *some* cover of
that member, and assembling those into a single cover of the base is a choice indexed by the
members of the cover; categorically that step is the commutation of a filtered colimit with
a product (the IPC property of Kashiwara–Schapira, *Categories and Sheaves*, §3.1, under
which §17.4 proves that `(P⁺)⁺` is a sheaf), which holds in a module category but is not a
consequence of AB5. The expected proof iterates the plus construction transfinitely; each
stage is left exact by the result above, and a filtered colimit of left exact functors is
left exact, so the exactness half of the argument is the part that is already in place.

-/

@[expose] public section

universe u' v u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Sheafification for `A`-valued presheaves on a small site `(C, J)`, for a Grothendieck
abelian coefficient category `A` whose `Hom`-types live in the universe of `C`.

**This is the one sorry of this development.** Left exactness of the plus construction over
such an `A` is proved in `WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact`
(`CategoryTheory.GrothendieckTopology.preservesFiniteLimits_plusFunctor'`); what is missing
is the sheaf condition, i.e. the construction of the reflector itself. Mathlib obtains it
from the plus construction only for a concrete `A`, its proof that `(P⁺)⁺` is a sheaf being
elementwise, and two steps of the plus construction are not known to suffice for a target
that is merely Grothendieck abelian. The expected proof iterates the plus construction
transfinitely; the exactness of each stage, and hence of the colimit, is the half that is
available. See the module docstring for the details. -/
theorem hasSheafify_of_isGrothendieckAbelian {C : Type v} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u') [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] :
    HasSheafify J A :=
  sorry

/-- Sheafification for `A`-valued presheaves on an essentially small site, for a
Grothendieck abelian coefficient category `A` with `Hom`-types in the universe `u + 1`: the
site is equivalent to a small one, to which
`CategoryTheory.GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian` applies.

All the other instances in this file are special cases. -/
instance (priority := high) hasSheafify_of_essentiallySmall (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {C : Type*} [Category* C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) :
    HasSheafify J A :=
  have : HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A :=
    hasSheafify_of_isGrothendieckAbelian _ A
  hasSheafifyEssentiallySmallSite J A

/-- Sheafification for `A`-valued presheaves on the small étale site of a scheme: the site
is essentially small in `u + 1`. -/
instance (priority := high) hasSheafify_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology A :=
  inferInstance

/-- Sheafification for `A`-valued presheaves on the localization of the small étale site
at an étale `U ⟶ X`: a slice of an essentially small site is again essentially small. This
is what lets a sheaf be restricted to a member of an étale cover without assuming
`HasWeakSheafify` for the localized site. -/
instance (priority := high) hasSheafify_over_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u})
    (U : X.Etale) :
    HasSheafify (X.smallEtaleTopology.over U) A :=
  inferInstance

/-- Sheafification for `A`-valued presheaves on the small pro-étale site of a scheme: the
site is essentially small in `u + 1`. -/
instance (priority := high) hasSheafify_proEtTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) A :=
  inferInstance

/-- Sheafification for `A`-valued presheaves on the localization of the small pro-étale
site at a weakly étale `U ⟶ X`: a slice of an essentially small site is again essentially
small. -/
instance (priority := high) hasSheafify_over_proEtTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u})
    (U : X.ProEt) :
    HasSheafify ((Scheme.ProEt.topology X).over U) A :=
  inferInstance

/-- Sheafification for `A`-valued presheaves on the small `Q`-site of `P`-schemes over a
scheme `U`, for a coefficient category `A` with small-site sheafification: the site has
objects in `Type (u + 1)` and `Hom`-types in `Type u`, so it is essentially `u + 1`-small. -/
instance (priority := high) hasSheafify_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [HasSmallSiteSheafify A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    HasSheafify (U.smallGrothendieckTopology Q (Q := P)) A :=
  HasSmallSiteSheafify.hasSheafify_of_essentiallySmall A _

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

end CategoryTheory.GrothendieckTopology
