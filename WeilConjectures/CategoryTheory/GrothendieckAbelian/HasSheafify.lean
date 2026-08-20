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
for a Grothendieck abelian category `A` with `Hom`-types in the universe `u` of the base
schemes: the sites are essentially small and `A` is complete and cocomplete with exact
filtered colimits, so the plus-construction applies and is left exact.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Sheafification for `A`-valued presheaves on the small `Q`-site of `P`-schemes over a
scheme `U`, for a Grothendieck abelian coefficient category `A` with `Hom`-types in the
universe `u` of the base schemes: the site is essentially small for the étale-like
properties `P` of interest and `A` is complete and cocomplete with exact filtered
colimits, so the plus-construction applies and is left exact. -/
instance (priority := high) hasSheafify_smallGrothendieckTopology (A : Type u')
    [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    HasSheafify (U.smallGrothendieckTopology Q (Q := P)) A :=
  sorry

/-- Sheafification for `A`-valued presheaves on the small étale site: the instance above
specialized to `P = Q = @Etale`. -/
instance (priority := high) hasSheafify_smallEtaleTopology (A : Type u')
    [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A] (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology A :=
  inferInstanceAs (HasSheafify (X.smallGrothendieckTopology (P := @Etale) (Q := @Etale)) A)

end CategoryTheory.GrothendieckTopology
