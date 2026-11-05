/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Adjunctions

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift

/-! # Pullback compatibility of the canonical derived-Hom class map

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-abelian-higher-direct-image-class-compatibility).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The free abelian sheaf on an etale representable, constructed by sheafification. -/
noncomputable abbrev abelianComparisonFree (S : Scheme.{v}) :=
  uliftYoneda.{v + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}

end AlgebraicGeometry.Etale
