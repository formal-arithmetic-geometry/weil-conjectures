/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!

# The sheaf categories on essentially small sites are Grothendieck abelian

The category of `A`-valued sheaves on an essentially small site is Grothendieck abelian,
for a Grothendieck abelian category `A` with `Hom`-types in the universe `u + 1`, one above
the universe `u` of the base schemes: the site is equivalent to a small one, so the sheaf
category is equivalent to a category of sheaves on a small site, which is Grothendieck
abelian. Since the site has `Hom`-types in `u`, the sheaf category again has `Hom`-types in
`u + 1`.

The small étale site is essentially small in `u + 1`, so this applies to it.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- The category of `A`-valued sheaves on an essentially small site is Grothendieck
abelian, for a Grothendieck abelian coefficient category `A` with `Hom`-types in the
universe `u + 1`, one above the universe `u` of the base schemes: the site is equivalent to
a small one, and sheafification is available on both by `hasSheafify_of_essentiallySmall`. -/
instance (priority := high) isGrothendieckAbelian_sheaf_of_essentiallySmall (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) :
    IsGrothendieckAbelian.{u + 1} (Sheaf J A) := by
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- The category of `A`-valued sheaves on the small étale site is Grothendieck abelian:
the instance above applied to the essentially small small étale site. -/
instance (priority := high) isGrothendieckAbelian_sheaf_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology A) :=
  inferInstance

end CategoryTheory.GrothendieckTopology
