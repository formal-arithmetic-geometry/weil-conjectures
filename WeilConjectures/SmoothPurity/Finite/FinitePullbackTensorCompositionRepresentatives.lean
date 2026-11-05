/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorChainComposition
import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeSquare
import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorCompositorFactors

/-! # Pullback composition on flat K-flat tensor representatives

Source: Stacks Project, Tags 07A4 and 00YV.
(blueprint: lem-pur-finite-pullback-tensor-composition-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
section TensorSquare
variable {K H D E : Type*} [Category K] [Category H] [Category D] [Category E]

end TensorSquare

namespace WeilConjectures
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf finiteIntrinsicDerivedTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

open FinitePullbackTensorRep
open CategoryTheory.Functor

end WeilConjectures
