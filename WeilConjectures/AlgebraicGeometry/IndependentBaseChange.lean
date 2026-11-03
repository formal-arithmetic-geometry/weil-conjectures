/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothBaseChangeCoefficients
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.Compactification.Dense
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersionBaseChange
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.EssImageKernels
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheaves
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.ClassicalProEtaleProperBaseChange

/-! # Independent base change with finite coefficients

Source: blueprint `sk-lem-tf-independent-base-change`, statement and proof, paragraphs 1–2
(blueprint: sk-lem-tf-independent-base-change).

The coefficient modules and bounded constructibility predicate are precisely the recorded
continuous-function coefficient-sheaf constructions. The exchange is the usual derived
adjunction mate, transported by the published exact coefficient realization equivalence.
This keeps the object in the specified ring-sheaf module derived category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The ordinary canonical product exchange in the recorded finite coefficient module
categories, using `prod.map_fst` for the square equality. Source: blueprint, displayed map
(blueprint: sk-lem-tf-independent-base-change).

Apply the inverse of the published exact coefficient realization to the input, take the
canonical mate of derived pullback composition, and realize the output. Thus both ends
are computed by ordinary uncompleted derived direct image and exact pullback through the
same coefficient equivalence. This is transport of the specified map, with no chosen
transformation or additional coefficient identification. -/
noncomputable def finiteCoefficientIndependentExchange {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (T : Over S) (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    (finiteCoefficientUnrealization X.left A).mapDerivedCategory ⋙
        R(lowerStar (ModuleCat.{u + 1} A) f.left) ⋙
        L(upperStar (ModuleCat.{u + 1} A) (prod.fst : Y ⨯ T ⟶ Y).left) ⋙
        (finiteCoefficientRealization (Y ⨯ T).left A).mapDerivedCategory ⟶
      (finiteCoefficientUnrealization X.left A).mapDerivedCategory ⋙
        L(upperStar (ModuleCat.{u + 1} A) (prod.fst : X ⨯ T ⟶ X).left) ⋙
        R(lowerStar (ModuleCat.{u + 1} A) (prod.map f (𝟙 T)).left) ⋙
        (finiteCoefficientRealization (Y ⨯ T).left A).mapDerivedCategory :=
  Functor.whiskerLeft (finiteCoefficientUnrealization X.left A).mapDerivedCategory
    (Functor.whiskerRight
      (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (show CommSq (prod.fst : X ⨯ T ⟶ X).left (prod.map f (𝟙 T)).left f.left
            (prod.fst : Y ⨯ T ⟶ Y).left from
          ⟨congrArg (fun a : X ⨯ T ⟶ Y ↦ a.left) (prod.map_fst f (𝟙 T)).symm⟩))
      (finiteCoefficientRealization (Y ⨯ T).left A).mapDerivedCategory)

end AlgebraicGeometry.ProEtale
