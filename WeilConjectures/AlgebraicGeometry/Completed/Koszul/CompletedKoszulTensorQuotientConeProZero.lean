/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentation
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulCoefficientConeRealization
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorConeComparison
import WeilConjectures.RingTheory.NoetherianKoszulAugmentationProZero
import WeilConjectures.AlgebraicGeometry.KoszulComplex
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.RingTheory.KoszulGeneratorChainMap
import WeilConjectures.RingTheory.KoszulProjectiveResolution
import WeilConjectures.RingTheory.KoszulPowerHomologyProZero
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Filtration
import WeilConjectures.RingTheory.KoszulConeHomologyProZero
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.Algebra.Homology.BoundedDerivedTowerProZero
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.CategoryTheory.Triangulated.ProZeroMiddle
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.RingTheory.Noetherian.Basic
import all WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement

/-! # Pro-zero cones of the completed strict Koszul tensor augmentation

Source: Stacks Project, Tags 0921 and 099M.
(blueprint: lem-weil-pbc-completed-koszul-tensor-quotient-cone-pro-zero).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] completedKoszulCochainMonoidal
  completedKoszulCochainMonoidalStruct

-- Preserve the inherited name hq in the statement.

end AlgebraicGeometry.Scheme
