/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!

# Sheafification on essentially small sites (sorried)

Sheafification exists for `A`-valued presheaves on any essentially small site, for a
Grothendieck abelian category `A` with `Hom`-types in the universe `u + 1`, one above the
universe `u` of the base schemes: the site is equivalent to a small one, and `A` is
complete and cocomplete with exact filtered colimits of size `u + 1`, so the
plus-construction applies and is left exact.

Everything in this file is deduced from that single statement
(`hasSheafify_essentiallySmall`), which is the only sorry: the small étale site, the small
pro-étale site and their localizations `J.over V` are essentially small in `u + 1`. The
localized instances are what lets the constructible-sheaf definitions of
`WeilConjectures.ConstructibleSheaf.Defs` restrict a sheaf to a member of an étale cover
without carrying `HasWeakSheafify` for the localized sites as a hypothesis.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Sheafification for `A`-valued presheaves on an essentially small site, for a
Grothendieck abelian coefficient category `A` with `Hom`-types in the universe `u + 1`: the
site is equivalent to a small one and `A` is complete and cocomplete with exact filtered
colimits of size `u + 1`, so the plus-construction applies and is left exact.

All the other instances in this file are special cases. -/
instance (priority := high) hasSheafify_essentiallySmall (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {C : Type*} [Category* C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) :
    HasSheafify J A :=
  sorry

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

end CategoryTheory.GrothendieckTopology
