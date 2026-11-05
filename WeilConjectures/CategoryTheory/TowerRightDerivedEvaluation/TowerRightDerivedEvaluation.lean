/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
public import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Unbounded right derivation commutes with tower evaluation

Source: Stacks Project, Sites Cohomology, Tag 0941, proof of
`lemma-derived-limit-is-ok`, and Derived Categories, Tags 070I, 070Y and 070K;
additive-functor generalization (blueprint: lem-coef-tower-right-derived-evaluation).

The units and resolution comparisons are those of
`Functor.rightDerivedFunctorOfQuasiIsoResolutions`. Natural number `n` denotes positive
level `n + 1`. No exactness or adjunction assumption is imposed on the additive functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TowerRightDerivedEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

end CategoryTheory.TowerRightDerivedEvaluation
