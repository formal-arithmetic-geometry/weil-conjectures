/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
public import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.RightDerivedExactComposite
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic

import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import Mathlib.CategoryTheory.Limits.Presheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Data.Finite.Prod

/-! # Classicality of coefficient-sized locally constant set sheaves

Source: Bhatt--Scholze, Lemmas 5.1.1--5.1.4.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory Opposite

namespace CategoryTheory.CoefficientClassical

end CategoryTheory.CoefficientClassical

namespace AlgebraicGeometry.Scheme.CoefficientClassical

-- The original sites with values in the independent coefficient universe.
private noncomputable abbrev comparison (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (toProEt X)
    (Type (max v (u + 1))) X.smallEtaleTopology (ProEt.topology X)

open Scheme in
open Scheme in
open Scheme in
open Scheme in
open Scheme in
end AlgebraicGeometry.Scheme.CoefficientClassical

namespace CategoryTheory.CoefficientClassical

end CategoryTheory.CoefficientClassical

namespace AlgebraicGeometry.Scheme.CoefficientClassical


private abbrev restriction (X : Scheme.{u}) (U : X.ProEt) :=
  @Functor.sheafPushforwardContinuous U.left.ProEt _ X.ProEt _
    (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop)
    (Type (max v (u + 1))) _ (ProEt.topology U.left) (ProEt.topology X)
    (ProEt.isContinuous_overMap U.prop)

end AlgebraicGeometry.Scheme.CoefficientClassical

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
