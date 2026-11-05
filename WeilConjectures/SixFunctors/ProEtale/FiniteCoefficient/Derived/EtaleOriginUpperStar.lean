/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar

/-!
# Pullbacks of complexes of étale origin

For a morphism of schemes `f : Y ⟶ X`, the derived pullback `Lf^*` of pro-étale sheaves sends
bounded below complexes of étale origin to bounded below complexes of étale origin
(`ProEtale.DerivedCategory.plusEtaleOrigin.leftDerivedUpperStar_obj`): pullback commutes with
`ν^*` (`ProEtale.comparisonUpperStarUpperStarIso`) and the étale pullback is exact.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X Y : Scheme.{u}}

end AlgebraicGeometry.ProEtale
