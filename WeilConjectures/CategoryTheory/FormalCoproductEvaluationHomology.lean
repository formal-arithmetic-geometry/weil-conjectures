/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.Grp.AB
/-!
# Homology preservation by formal coproduct evaluation
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

instance formalCoproductEval_preservesZero
    {C : Type u} [Category.{v} C] (X : (FormalCoproduct.{v} C)ᵒᵖ) :
    ((FormalCoproduct.evalOp C AddCommGrpCat.{v}) ⋙
      (evaluation _ AddCommGrpCat).obj X).PreservesZeroMorphisms where
  map_zero := by
    intro P Q
    apply Pi.hom_ext
    intro i
    simp [FormalCoproduct.evalOp]

/-- Evaluation on a formal coproduct preserves homology of short complexes of
abelian presheaves. -/
theorem formalCoproductEval_preservesHomology
    {C : Type u} [Category.{v} C] (X : (FormalCoproduct.{v} C)ᵒᵖ) :
    ((FormalCoproduct.evalOp C AddCommGrpCat.{v}) ⋙
      (evaluation _ AddCommGrpCat).obj X).PreservesHomology := by
  let T : Discrete X.unop.I ⥤ Cᵒᵖ :=
    Discrete.functor (fun i ↦ Opposite.op (X.unop.obj i))
  let G := (Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj T ⋙ lim
  let e : ((FormalCoproduct.evalOp C AddCommGrpCat.{v}) ⋙
      (evaluation _ AddCommGrpCat).obj X) ≅ G :=
    NatIso.ofComponents (fun P ↦ Pi.isoLimit (T ⋙ P)) (by
      intro P Q α
      apply limit.hom_ext
      intro ⟨i⟩
      simp [G, T, FormalCoproduct.evalOp, Pi.isoLimit_hom_π])
  have : PreservesFiniteLimits G := inferInstance
  have : PreservesFiniteColimits G := inferInstance
  have := preservesFiniteLimits_of_natIso e.symm
  have := preservesFiniteColimits_of_natIso e.symm
  infer_instance

end CategoryTheory
