/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitStrictWitness
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitStrictEquationAssembly
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitRepresentativeTransport

/-! # Assembly of strict scalar/tensor representatives

Source: Stacks 07A4 and 0941; localization and total-limit transport in
realization step 8 of `lem-pur-scalar-extension-tower-coherence`.

The remaining assembly takes strict representative witnesses as input and
passes them through the localization, completion, realization and total-limit
maps.  It is separated from the strict representative calculation so that the
two arguments can be proved independently.
(blueprint: stage3-pur-scalar-tensor-limit-transport-assembly)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible]
  integralCompletedTensor integralDerivedPullback
  integralComparisonDerivedSequenceScalar integralComparisonDerivedSequencePullback
  pullbackReduction scalarReduction tensorReduction

end WeilConjectures.ScalarExtensionTower
