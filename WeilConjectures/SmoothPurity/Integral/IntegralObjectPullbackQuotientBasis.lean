/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.SmoothPurity.IntegralObjectQuotient.IntegralObjectFiniteBasis
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.ConstantScalarStrictUnit.ConstantScalarStrictUnit

/-! # Compatible quotient bases after inverse image along a site object

Source: Stacks Project, Modules on Sites, localization at an object (Tag 04J0);
Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9.
(blueprint: lem-pur-integral-object-pullback-quotient-basis).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] constantSheaf CategoryTheory.Limits.limit
  HasDerivedCategory.standard
  unrestrictedIntegralReductionExistence unrestrictedIntegralReductionFunctor
  completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingProjectionUnrestricted
  AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction
  AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback Functor.leftAdjoint
  IntegralObjectQuotient.basisSection
  integralScalarTransition integralScalarReduction integralScalarReductionConcrete
  integralScalarReductionWitness

attribute [local instance 5000] integralObjectPullbackSiteSmall

namespace IntegralObjectQuotientProof

open IntegralObjectQuotient

section RestrictionLemmas
universe a b r
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{r}} (q : R ⟶ S)
  {M : SheafOfModules.{r} R} {N : SheafOfModules.{r} S}
  (f : M ⟶ (SheafOfModules.restrictScalars q).obj N)

end RestrictionLemmas

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] unrestrictedIntegralTensorSection integralOperationsPullbackGenerator

attribute [local irreducible] integralPullbackFiniteComplexMap
  integralOperationsPullbackTransition SheafOfModules.IntegralScalarProof.restrictComplexMap

attribute [local irreducible] nativeFiniteMap

attribute [local irreducible] finiteAbMap forgetModuleMap

variable (X : Scheme.{u}) (W : X.ProEt) (L : integralTowerModules.{u, u} l E X)
  (e : L.over W ≅
    (SheafOfModules.unit.{u, u + 1, u + 1}
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).over W)

attribute [local irreducible] IntegralObjectQuotient.basisGenerator

end IntegralObjectQuotientProof

end WeilConjectures
