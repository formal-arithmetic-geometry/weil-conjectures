/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleCoherentTotalTensorPullbackComparison
import WeilConjectures.SmoothPurity.Ringed.RingedDerivedTensorComparisonAssociativity
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatRepresentatives
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatDiagrams
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement

/-! # Associativity on flat K-flat pullback tensor representatives

Source: Stacks Project, Tags 07A4, 06YS and 03EL.
(blueprint: lem-pur-finite-pullback-tensor-associativity-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory.MonoidalCategory
open CategoryTheory.RingedForgetTensorTransposition
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
  finiteIntrinsicClosed finiteIntrinsicTensorModels
  proEtaleTensorPullbackTotalIso proEtaleTensorPullbackTotal
  SheafOfModules.monoidalCategory coefficientTensorGenerator
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  finiteIntrinsicDerivedTensor coefficientTotalTensor coefficientKFlatInclusion
  coefficientFiniteInternalHom FinitePullbackTensorRep.totalTensor
  CoefficientClosedStructure.tensor
attribute [local semireducible] FinitePullbackTensorRep.pull
attribute [local implicit_reducible] FinitePullbackTensorRep.pull

attribute [local instance 4000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived FinitePullbackTensorRep.ordinary_additive
  FinitePullbackTensorRep.ordinary_limits FinitePullbackTensorRep.ordinary_colimits
attribute [local implicit_reducible] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived

end WeilConjectures
