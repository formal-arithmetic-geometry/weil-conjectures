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

This file introduces the class `CategoryTheory.SmallSiteCoefficients A` recording
sheafification of `A`-valued presheaves on every site with objects in `Type (u + 1)` and
`Hom`-types in `Type u`. It is the single hypothesis on the coefficient category, next to
Grothendieck abelianness, that the six-functor formalism assumes; the intended instances
are the concrete categories `ModuleCat.{u + 1} Λ` and `Ab.{u + 1}`, for which the class is
inferred from Mathlib's sheafification (see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Instances`).

## Main declarations

- `CategoryTheory.SmallSiteCoefficients`: the class.
- `CategoryTheory.SmallSiteCoefficients.isGrothendieckAbelian_sheaf`: for `A` Grothendieck
  abelian with `SmallSiteCoefficients A`, the sheaf categories on such sites are again
  Grothendieck abelian.

-/

@[expose] public section

universe u' u

namespace CategoryTheory

open Limits

/-- A category `A` with `Hom`-types in the universe `u + 1` has *small site coefficients*
if `A`-valued presheaves on every site with objects in `Type (u + 1)` and `Hom`-types in
`Type u` admit a left exact sheafification. This is the case for the concrete Grothendieck
abelian categories `ModuleCat.{u + 1} Λ` and `Ab.{u + 1}`, and holds (but is not available in
Mathlib) for every Grothendieck abelian category of size `u + 1`. The small sites of
`P`-schemes over a scheme in `Scheme.{u}`, and their localizations, are sites of this
kind. -/
class SmallSiteCoefficients (A : Type u') [Category.{u + 1} A] : Prop where
  hasSheafify {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) : HasSheafify J A

attribute [instance] SmallSiteCoefficients.hasSheafify

namespace SmallSiteCoefficients

variable (A : Type u') [Category.{u + 1} A] [SmallSiteCoefficients A]

/-- The category of `A`-valued sheaves on a site with objects in `Type (u + 1)` and
`Hom`-types in `Type u` is Grothendieck abelian, for `A` Grothendieck abelian with small
site coefficients: the site is essentially `u + 1`-small. -/
lemma isGrothendieckAbelian_sheaf [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    IsGrothendieckAbelian.{u + 1} (Sheaf J A) :=
  have : EssentiallySmall.{u + 1} C := inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify J A

end SmallSiteCoefficients

end CategoryTheory
