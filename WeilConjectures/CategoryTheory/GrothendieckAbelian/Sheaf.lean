/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!

# The sheaf categories on the small sites are Grothendieck abelian (sorried)

The category of `A`-valued sheaves on the small `Q`-site of `P`-schemes is Grothendieck
abelian, for a Grothendieck abelian category `A` with `Hom`-types in the universe `u + 1`,
one above the universe `u` of the base schemes: the site is essentially small, so the
sheaf category is equivalent to a category of sheaves on a small site, which is
Grothendieck abelian. Since the site has `Hom`-types in `u`, the sheaf category again has
`Hom`-types in `u + 1`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- The category of `A`-valued sheaves on an essentially small site is Grothendieck
abelian, for a Grothendieck abelian coefficient category `A` with `Hom`-types in the
universe `u + 1`, one above the universe `u` of the base schemes: the site is equivalent to
a small one, and sheafification is available on both by `hasSheafify_essentiallySmall`.

All the other instances in this file are special cases. -/
instance (priority := high) isGrothendieckAbelian_sheaf_essentiallySmall (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) :
    IsGrothendieckAbelian.{u + 1} (Sheaf J A) := by
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- The category of `A`-valued sheaves on the small `Q`-site of `P`-schemes over a scheme
`U` is Grothendieck abelian, for a Grothendieck abelian coefficient category `A` with
`Hom`-types in the universe `u + 1`, one above the universe `u` of the base schemes: the
site is essentially small for the étale-like properties `P` of interest, so the sheaf
category is equivalent to a category of sheaves on a small site, which is Grothendieck
abelian. -/
instance isGrothendieckAbelian_sheaf_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) :=
  inferInstance

/-- The category of `A`-valued sheaves on the small étale site is Grothendieck abelian:
the instance above specialized to `P = Q = @Etale`. -/
instance (priority := high) isGrothendieckAbelian_sheaf_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology A) :=
  inferInstanceAs (IsGrothendieckAbelian.{u + 1}
    (Sheaf (X.smallGrothendieckTopology (P := @Etale) (Q := @Etale)) A))

/-- The category of `A`-valued sheaves on the small pro-étale site is Grothendieck
abelian: it is essentially small in `u + 1`. -/
instance (priority := high) isGrothendieckAbelian_sheaf_proEtTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (Y : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (Scheme.ProEt.topology Y) A) :=
  inferInstance

end CategoryTheory.GrothendieckTopology
