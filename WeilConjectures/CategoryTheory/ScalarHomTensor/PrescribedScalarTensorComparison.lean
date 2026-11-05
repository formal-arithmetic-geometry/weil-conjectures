/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarHomExtensionKFlat
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Normalized scalar tensor comparison on unbounded derived categories

Source: Stacks Project, Cohomology on Sites, Tag 07A4.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w u u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Functor
open SheafOfModules WeilConjectures
namespace CategoryTheory.ScalarHomTensor
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
  [∀ R : Sheaf J CommRingCat.{max c v r},
    HasDerivedCategory.{w} (scalarModules J R)]
  (s : ScalarDerivedPair a)
  (SR : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
  (SS : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S))
  (TR : CoefficientTensorModels.{r, c, v, w} J R SR)
  (TS : CoefficientTensorModels.{r, c, v, w} J S SS)

attribute [local irreducible] pairTensorNormalization

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] monoidalCategory scalarPairComplexComparison
  CoefficientTensorModels.iso

end CategoryTheory.ScalarHomTensor
