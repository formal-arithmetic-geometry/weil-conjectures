/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicOrdinaryTensorDiagram

/-! # The consecutive square for ordinary algebraic quotient tensors

Source: Stacks Project, More on Algebra, Tag 09AW; More on Algebra, Tag 06Y6.
(blueprint: lem-weil-pbc-adic-ordinary-tensor-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible] adicOrdinaryQuotientComplexIso adicOrdinaryTensorComplexDiagram
attribute [local irreducible] adicOrdinaryTensorLevelMap

end AlgebraicGeometry.Scheme
