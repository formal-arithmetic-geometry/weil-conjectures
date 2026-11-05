/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import WeilConjectures.CategoryTheory.StageSystem.Preadditive
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.Set.Finite.Lattice

/-! # Coherent common-stage pair functor descent

Source: blueprint sketches 32, finite common-stage principle, and 42,
Proposition `prop:pseudocone-functor`, Theorems `thm:pair-universal` and
`thm:karoubi-universal` (blueprint: lem-sbc-coherent-pair-functor-descent).
-/

@[expose] public section

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CommonStage

-- Bundling the category carriers puts both independent category universes in a maximum.

attribute [instance] Diagram.category Diagram.preadditive Diagram.biproducts Diagram.additive

variable {I : Type w} [PartialOrder I]

attribute [instance] Family.additive

-- The independently variable object and Hom universes are bundled in the same maximum.
set_option linter.checkUnivs false in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

set_option allowUnsafeReducibility true in
attribute [local reducible] PairStructure.Obj Pair

end CategoryTheory.CommonStage
