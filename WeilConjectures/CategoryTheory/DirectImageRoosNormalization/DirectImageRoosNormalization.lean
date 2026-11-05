/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import WeilConjectures.CategoryTheory.Strict.StrictRoosAdditiveComparison
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Normalized direct image of canonical Roos triangles

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0941; Derived Categories,
Tag 0BK6, with the explicit strict cone normalization in the DAG
(blueprint: lem-weil-pbc-direct-image-roos-normalization).

The structures below only package the choices of total derived functors, units and
canonical comparisons already appearing in the statement. The conclusion constructs
Roos triangles with normalization on every complex, rather than choosing cone vertices
up to an unspecified isomorphism. The index `n : ℕ` denotes positive level `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w uA vA uB vB g

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory
namespace DirectImageRoosNormalization

section PrivateElementary

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts

end PrivateElementary

variable (A : Type uA) [Category.{vA} A] [Abelian A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

variable {A}
variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

variable [HasCountableProducts A] [HasCountableProducts (DerivedCategory.{w} A)]

section PrivateComparisons

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts

end PrivateComparisons

section PrivateTriangles

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts

end PrivateTriangles

variable [HasCountableProducts (DerivedCategory.{w} B)]

variable [HasCountableProducts B]

section PrivateSquares

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts

end PrivateSquares

end DirectImageRoosNormalization

open DirectImageRoosNormalization

end CategoryTheory
