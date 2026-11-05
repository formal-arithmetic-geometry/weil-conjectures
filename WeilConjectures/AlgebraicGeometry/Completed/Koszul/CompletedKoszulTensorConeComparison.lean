/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulCoefficientConeRealization
import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorConeComparisonAux
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorAugmentationComponent

/-! # Tensor comparison for normalized completed Koszul augmentation cones

Source: Stacks Project, Tags 099M and 06YP; the signed total-tensor cone formula.
(blueprint: lem-weil-pbc-completed-koszul-tensor-cone-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] completedKoszulCochainMonoidal
  completedKoszulCochainMonoidalStruct
attribute [local instance] Functor.preservesZeroMorphisms_of_additive

attribute [local irreducible] completedAdicRing

end AlgebraicGeometry.Scheme
