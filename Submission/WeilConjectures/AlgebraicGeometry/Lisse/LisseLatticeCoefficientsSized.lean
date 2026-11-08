/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Submission.WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficients

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Continuous coefficients in the universe of module values

Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3
(blueprint: def-weil-pbc-lisse-lattice-coefficients).
The coefficient universe is allowed to be the larger site universe. The old
small-coefficient constructions and slice-site inclusion remain available.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The existing pointwise continuous-function presheaf, retaining commutativity.
Source: Bhatt--Scholze, Definition 6.8.1.
(blueprint: def-weil-pbc-lisse-lattice-coefficients) -/
def lisseContinuousCommRingPresheafUniverses (X : Scheme.{u}) (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{max (u + 1) v} where
  obj U := CommRingCat.of (ULift.{u + 1} C(U.unop.left, T))
  map f := CommRingCat.ofHom ((continuousMapRingPresheaf X T).map f).hom
  map_id _ := rfl
  map_comp _ _ := rfl

end AlgebraicGeometry.ProEtale
