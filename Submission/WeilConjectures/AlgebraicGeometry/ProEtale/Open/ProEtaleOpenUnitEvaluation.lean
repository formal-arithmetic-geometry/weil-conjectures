/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import Mathlib.Algebra.Category.Ring.Limits
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.ShortExact
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Sites.Equivalence
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Open pro-etale pullback evaluation and its specified adjunction unit

Source: Stacks Project, Tags 09BN, 00VE, 00WH, 00WX, 00XZ and 03D3
(blueprint: lem-pur-proetale-open-unit-evaluation).

The pullback and unit are the published small-model module constructions.
The coefficient comparison below is normalized on constant sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Compose a pro-etale object's structure map with an open immersion, retaining its
underlying scheme and arrows. Source: Stacks Project, Tags 00XZ and 09BN
(blueprint: lem-pur-proetale-open-unit-evaluation). -/
def proEtaleOpenComposition {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    U.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

end AlgebraicGeometry.Scheme
