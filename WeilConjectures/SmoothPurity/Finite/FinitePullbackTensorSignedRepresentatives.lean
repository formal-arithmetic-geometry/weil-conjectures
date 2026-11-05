/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleSignedTensorPullbackTotal

/-! # Signed exchange on flat K-flat representatives

Source: Stacks 07A4, lemma-pullback-tensor-product, with the symmetry paragraph
after definition-derived-tor (06YU) and the signs of 0FNG.
(blueprint: lem-pur-finite-pullback-tensor-signed-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local implicit_reducible] pullbackTensorSwap
attribute [local implicit_reducible] coefficientTotalTensor Functor.map₂HomologicalComplex
  CoefficientTensorModels.iso coefficientFiniteInternalHom finiteIntrinsicDerivedTensor
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction pullbackTensorBraiding
  proEtaleTensorPullbackTotal proEtaleTensorPullbackTotalIso proEtaleRingDerivedPullbackFactors
  pullbackTensorSignedTotal HomologicalComplex₂.total
  CategoryTheory.Functor.mapBifunctorHomologicalComplex

attribute [local implicit_reducible] tensorModelRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures
