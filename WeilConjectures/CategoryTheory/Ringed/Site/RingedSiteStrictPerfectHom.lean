/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.SixFunctors.Supporting.RingedSiteHomComponentProjection
import WeilConjectures.CategoryTheory.RingedSiteBoundedDual.RingedSiteBoundedDualComponents
import WeilConjectures.CategoryTheory.RingedSiteBoundedEvaluation.RingedSiteBoundedEvaluationAssembly
import WeilConjectures.Algebra.Homology.Ringed.RingedSiteFiniteRetractDualExact
import WeilConjectures.CategoryTheory.SplitPerfectHom.IndependentBoundedExactTermHom
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.SmoothPurity.PullbackDualFreeChart

/-! # Ordinary Hom calculations for a bounded finite-free retract complex

Source: Stacks Project, sites-cohomology.tex, Tags 08JH and 08JJ,
lemma-Rhom-strictly-perfect and lemma-dual-perfect-complex.
(blueprint: lem-sfb-ringed-site-strict-perfect-hom).
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.RingedSiteBoundedDual.modulesHasZeroObject
  CategoryTheory.RingedSiteBoundedEvaluation.smallColimits
  CategoryTheory.RingedSiteBoundedEvaluation.hasTotal
  CategoryTheory.RingedSiteBoundedEvaluation.finiteBiproducts
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace PresheafOfModules
variable {C : Type c} [Category.{v} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{max c v r}}
  (N : PresheafOfModules.{max c v r} (R ⋙ forget₂ _ _))

end PresheafOfModules

namespace CategoryTheory
open MonoidalCategory
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local irreducible] SheafOfModules.monoidalCategory homComplexFunctor homComplexπ
  SheafOfModules.tensorObjIsoSheafification
  ringedSiteOrdinaryEvaluation ringedSiteOrdinaryBidual

noncomputable section Private

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- Name the category and its canonical structures so instance inference need not
rebuild the sheaf-category constructions in each finite-retract calculation. -/
@[implicit_reducible, no_expose] private def StrictPerfectModules :=
  SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

set_option hygiene false in
local notation "𝓜" => StrictPerfectModules.{c, v, r} J R

section AssemblyProof
attribute [local semireducible] SheafOfModules.monoidalCategory

end AssemblyProof

end Private

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

end CategoryTheory
