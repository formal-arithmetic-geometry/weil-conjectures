/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!

# Coefficient categories for sheaves on the small sites

The six-functor files of this project work with sheaves on the small sites of `P`-schemes
over a scheme `U : Scheme.{u}` with values in a Grothendieck abelian category `A` with
`Hom`-types in the universe `u + 1`. Beyond Grothendieck abelianness of `A`, they need
sheafification of `A`-valued presheaves on these sites and on their localizations. These
sites have objects in `Type (u + 1)` and `Hom`-types in `Type u`, so they are essentially
`u + 1`-small; sheafification with values in a Grothendieck abelian category of that size
exists for such sites by the plus-construction (filtered colimits of size `u + 1` are exact
in `A`), but Mathlib only provides it for *concrete* coefficient categories
(`CategoryTheory.HasSheafify` via `Mathlib/CategoryTheory/Sites/LeftExact.lean`, which needs
`PreservesLimits (forget A)`).

This file introduces the class `CategoryTheory.HasSmallSiteSheafify A` recording
sheafification of `A`-valued presheaves on every `u + 1`-small site. It is the single
hypothesis on the coefficient category, next to Grothendieck abelianness, that the
six-functor formalism assumes; the intended instances are the concrete categories
`ModuleCat.{u + 1} Λ` and `AddCommGrpCat.{u + 1}`, for which the class is inferred from
Mathlib's sheafification (see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`).

## TODO

The class is scaffolding around a gap in Mathlib, not a permanent part of the API. The
missing theorem is: *for `A` Grothendieck abelian of size `u + 1` and `(C, J)` a `u + 1`-small
site, the plus-construction sheafification of `A`-valued presheaves on `(C, J)` exists and is
left exact.* Indeed the plus-construction is a filtered colimit of matching objects, which
are limits, so AB5 and completeness of `A` suffice; Mathlib's
`Mathlib/CategoryTheory/Sites/LeftExact.lean` instead proves left exactness through
`forget A`, which is why concreteness enters. Once that theorem is available,
`CategoryTheory.HasSmallSiteSheafify` becomes a consequence of
`CategoryTheory.IsGrothendieckAbelian` and this class (together with the hypothesis in the
files that carry it) should be deleted.

## Main declarations

- `CategoryTheory.HasSmallSiteSheafify`: the class.
- `CategoryTheory.HasSmallSiteSheafify.hasSheafify_of_essentiallySmall`: the class gives
  sheafification on every essentially `u + 1`-small site, not only on the `u + 1`-small ones.
- `CategoryTheory.Sheaf.isGrothendieckAbelian_of_hasSmallSiteSheafify`: for `A` Grothendieck
  abelian with `HasSmallSiteSheafify A`, the sheaf categories on essentially `u + 1`-small
  sites are again Grothendieck abelian.

-/

@[expose] public section

universe u' u v₂ u₂

namespace CategoryTheory

open Limits

/-- A category `A` with `Hom`-types in the universe `u + 1` has *small-site sheafification*
if `A`-valued presheaves on every `u + 1`-small site admit a left exact sheafification. This
is the case for the concrete Grothendieck abelian categories `ModuleCat.{u + 1} Λ` and
`AddCommGrpCat.{u + 1}`, and holds (but is not available in Mathlib) for every Grothendieck
abelian category of size `u + 1`. The small sites of `P`-schemes over a scheme in
`Scheme.{u}`, and their localizations, are essentially `u + 1`-small, so the class applies to
them through `CategoryTheory.HasSmallSiteSheafify.hasSheafify_of_essentiallySmall`. -/
class HasSmallSiteSheafify (A : Type u') [Category.{u + 1} A] : Prop where
  hasSheafify {C : Type (u + 1)} [Category.{u + 1} C] (J : GrothendieckTopology C) :
    HasSheafify J A

namespace HasSmallSiteSheafify

variable (A : Type u') [Category.{u + 1} A] [HasSmallSiteSheafify A]

/-- The class asks for sheafification on `u + 1`-small sites only, but it gives it on every
essentially `u + 1`-small site: sheafification transports along the equivalence with the small
model (`CategoryTheory.hasSheafifyEssentiallySmallSite`).

This is deliberately *not* an instance: its conclusion `HasSheafify J A` matches every
sheafification goal in the library. The sites this project needs it for get their own
instances in `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, keyed on the
small sites, so that instance search is not attempted on unrelated `HasSheafify` goals. -/
lemma hasSheafify_of_essentiallySmall {C : Type u₂} [Category.{v₂} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) : HasSheafify J A :=
  have := HasSmallSiteSheafify.hasSheafify (A := A)
    ((equivSmallModel.{u + 1} C).inverse.inducedTopology J)
  hasSheafifyEssentiallySmallSite J A

end HasSmallSiteSheafify

attribute [local instance] HasSmallSiteSheafify.hasSheafify_of_essentiallySmall in
/-- The category of `A`-valued sheaves on an essentially `u + 1`-small site is Grothendieck
abelian, for `A` Grothendieck abelian with small-site sheafification. -/
lemma Sheaf.isGrothendieckAbelian_of_hasSmallSiteSheafify (A : Type u') [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {C : Type u₂} [Category.{v₂} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) :
    IsGrothendieckAbelian.{u + 1} (Sheaf J A) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall' J A

end CategoryTheory
