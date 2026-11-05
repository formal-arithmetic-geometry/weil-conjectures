/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeData
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData

/-! # Naturality of the two finite tensor comparison composites

Source: Stacks Tags 06YS and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-kflat-diagrams).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u v w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
  finiteIntrinsicClosed finiteIntrinsicTensorModels
  proEtaleTensorPullbackTotalIso proEtaleTensorPullbackTotal
  proEtaleOrdinaryTensorPullback SheafOfModules.monoidalCategory
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  finiteIntrinsicDerivedTensor
  coefficientTotalTensor coefficientKFlatInclusion coefficientFiniteInternalHom
  FinitePullbackTensorRep.totalTensor
attribute [local semireducible] FinitePullbackTensorRep.pull
attribute [local implicit_reducible] FinitePullbackTensorRep.pull
  CategoryTheory.Functor.map₂HomologicalComplex CategoryTheory.Functor.mapHomologicalComplex
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived FinitePullbackTensorRep.ordinary_additive
  FinitePullbackTensorRep.ordinary_limits FinitePullbackTensorRep.ordinary_colimits
attribute [local implicit_reducible] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived

/-- Restrict the prescribed tensor-model comparison to a family of K-flat complexes.
Source: Stacks 06YS (blueprint: lem-pur-finite-pullback-tensor-kflat-diagrams). -/
@[irreducible] def finiteTensorModelOnKFlatFamily (W : Scheme.{u}) (n : ℕ)
    {C : Type v} [Category.{w} C]
    (I : C ⥤ CochainComplex (normalizedDVRModules l E W n) ℤ)
    (h : ∀ K, CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) (I.obj K)) :
    (I.prod I) ⋙ FinitePullbackTensorRep.totalTensor l E W n ⋙ DerivedCategory.Q ≅
      ((I ⋙ DerivedCategory.Q).prod (I ⋙ DerivedCategory.Q)) ⋙
        finiteIntrinsicDerivedTensor l E W n := by
  let KP : ObjectProperty (CochainComplex (normalizedDVRModules l E W n) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n)
  let j := KP.lift I h
  exact isoWhiskerLeft (j.prod j) (finiteIntrinsicTensorModels l E W n).comparison

end WeilConjectures
