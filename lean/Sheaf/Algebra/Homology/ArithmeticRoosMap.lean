/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictRoosAdditiveComparison

/-! # The canonical arithmetic Roos map

This name keeps the source and target expressed in the functorial Roos model.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe x y
open CategoryTheory CategoryTheory.Limits CategoryTheory.StrictTowerArithmetic
namespace CategoryTheory.PrincipalQuotientCompletion

/-- The actual arithmetic Roos map from selection and finite-block summation.
This is the already defined map of the corresponding commuting square.
Source: Stacks 0H9K, DAG proof steps 6--7
(blueprint: def-pur-arithmetic-roos-map). -/
noncomputable def arithmeticRoosMap
    {A : Type x} [Category.{y} A] [Abelian A] [HasCountableProducts A]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (e : ℕ) (he : 1 ≤ e) :
    roosF.obj X ⟶ roosF.obj ((complexRestriction A e).obj X) :=
  strictRoosMapOfSquare (selection e X.asFunctor) (block e X.asFunctor)
    (strictRoosBlock_comm X e he)


end CategoryTheory.PrincipalQuotientCompletion
