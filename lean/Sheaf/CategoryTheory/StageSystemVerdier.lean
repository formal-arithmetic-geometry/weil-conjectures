/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.CategoryTheory.StageSystemCommonStageCones
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-! # The Verdier axioms for common-stage triangles

Source: blueprint `sec-proper-base-change/sk-thm-properbasechange`, Verdier axioms
(blueprint: thm-weil-pbc-verdier-axioms).
-/

@[expose] public section
set_option autoImplicit false

universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
  [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i, HasShift (C i) ℤ] [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] [∀ i, IsTriangulated (C i)]
  [Preadditive S.PairCategory] [HasZeroObject S.PairCategory]
  [HasShift S.PairCategory ℤ] [∀ n : ℤ, (shiftFunctor S.PairCategory n).Additive]
  [∀ i, (S.ι i).Additive] [∀ i, (S.ι i).CommShift ℤ]
  [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ (i j : I) (h : i ≤ j), (S.T h).IsTriangulated]
  [∀ (i j : I) (h : i ≤ j), NatTrans.CommShift (S.transIso h).hom ℤ]

/-- Common-stage triangles satisfy TR1--TR4; stage inclusions and transition
identifications are exact. The distinguished set uniquely fixes the pretriangulation.
Source: blueprint Verdier axioms (blueprint: thm-weil-pbc-verdier-axioms).
Proof: move every finite collection of objects and arrows to a common stage using
StageSystem.PairCategory.exists_common_stage. Equalities hold after one further
extension by mkHom_eq_mkHom_iff. At that stage choose cone and identity triangles;
apply signed rotation and the completion of a commutative square. Exact transitions
and the coherent shift comparisons preserve these operations. Isomorphism closure
is in the definition. This proves TR1--TR3. Move the composable arrows and their
three cone triangles to one stage, enlarge to descend all commuting equations,
and apply its octahedral axiom. Its image gives TR4. The image of every stage
triangle is distinguished by definition; transIso commutes with shifts by the
specified stage coherence, so these are exact natural isomorphisms. Finally a
Pretriangulated structure has only its distinguished set as non-propositional data,
so the displayed criterion proves uniqueness. -/
theorem commonStage_verdier_existsUnique :
    ∃! t : Pretriangulated S.PairCategory,
      (fun [triInst : Pretriangulated S.PairCategory] ↦
        (∀ T : Triangle S.PairCategory,
          T ∈ distTriang S.PairCategory ↔ S.CommonStageDistinguished T) ∧
        IsTriangulated S.PairCategory ∧ ∀ i : I, (S.ι i).IsTriangulated)
        (triInst := t) := by
  sorry

end CategoryTheory.StageSystem
