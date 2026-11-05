/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentation
public import WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientRealization
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulUnitTensorRealization
import WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
import WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement

/-! # Finite exact realization of completed Koszul coefficient cones

Source: Stacks Project, Tags 099M, 0921 and 093M.
(blueprint: lem-weil-pbc-completed-koszul-coefficient-cone-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [-instance] completedKoszulCochainMonoidal
attribute [local instance] completedKoszulCochainMonoidal

attribute [-instance] completedKoszulCochainMonoidalStruct
attribute [local instance] completedKoszulCochainMonoidalStruct

attribute [local instance] koszulConstantFunctor_preservesZero

end AlgebraicGeometry.Scheme
