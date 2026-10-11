/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjection

/-!
# The comparison carries the étale projection map of `Rg_*` to the pro-étale one
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

lemma Etale.leftDerivedUpperStarTensorComparison_eq [Etale.UpperStarPreservesFlat A] :
    Etale.leftDerivedUpperStarTensorComparison A g =
      (Etale.upperStar A g).leftDerivedTensorComparison :=
  rfl

lemma ProEtale.leftDerivedUpperStarTensorComparison_eq [ProEtale.UpperStarPreservesFlat A] :
    ProEtale.leftDerivedUpperStarTensorComparison A g =
      (ProEtale.upperStar A g).leftDerivedTensorComparison :=
  rfl

end AlgebraicGeometry
