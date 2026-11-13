/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

/-!
# Canonical derived direct-image comparison as a mate

Source: Stacks Tags 099R and 0B65.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The named bounded-below derived direct-image comparison is the mate of the
canonical pullback comparison.  This is the objectwise map used in the
proper-base-change comparison theorem.

Source: Stacks Tag 0B65. -/
noncomputable def comparisonDirectImageCanonicalMate (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (u : U ⟶ V) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) u ⋙
        D+((comparisonUpperStar (ModuleCat.{u + 1} Λ) V)) ⟶
      D+((comparisonUpperStar (ModuleCat.{u + 1} Λ) U)) ⋙
        R+((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) u)) :=
  Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange u (ModuleCat.{u + 1} Λ))

/-- The canonical comparison is an isomorphism for quasi-compact,
quasi-separated morphisms.  Its component is the named mate, hence this
asserts invertibility of that particular morphism.

Source: Stacks Tag 099R. -/
theorem isIso_comparisonDirectImageCanonicalMate (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {U V : Scheme.{u}} (u : U ⟶ V)
    [QuasiCompact u] [QuasiSeparated u] :
    IsIso (comparisonDirectImageCanonicalMate Λ u) := by
  exact isIso_comparisonDirectImagePlus Λ u

end AlgebraicGeometry.ProEtale
