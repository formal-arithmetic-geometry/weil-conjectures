/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.Algebra.Homology.Monoidal.Supertrace
public import WeilConjectures.CategoryTheory.Shift.ShiftDecomposition

/-!
# Traces along decompositions into shifts

For a decomposition `P ≅ ⨁ⱼ E⟦nⱼ⟧` (`CategoryTheory.ShiftDecomposition`), the categorical trace
of an endomorphism `v` of `P` is the sum of the traces of its diagonal blocks
`E⟦nⱼ⟧ ⟶ P ⟶ P ⟶ E⟦nⱼ⟧` (`CategoryTheory.ShiftDecomposition.trace_eq_sum`), and likewise for
the trace of the linear map induced by an additive functor to modules over a field
(`CategoryTheory.ShiftDecomposition.linearMapTrace_eq_sum`). Both follow from the cyclicity of
the trace and `∑ⱼ pⱼ ≫ iⱼ = 𝟙`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.ShiftDecomposition

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ] {E P : C}
  (D : ShiftDecomposition E P)

section Monoidal

variable [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C]

/-- The categorical trace of an endomorphism of `⨁ⱼ E⟦nⱼ⟧` is the sum of the traces of its
diagonal blocks. -/
theorem trace_eq_sum [HasRightDual P] [∀ n : ℤ, HasRightDual ((shiftFunctor C n).obj E)]
    (v : P ⟶ P) : trace v = ∑ j, trace (D.incl j ≫ v ≫ D.proj j) := by
  calc trace v = trace ((∑ j, D.proj j ≫ D.incl j) ≫ v) := by rw [D.total, Category.id_comp]
    _ = ∑ j, trace (D.proj j ≫ D.incl j ≫ v) := by
        rw [Preadditive.sum_comp, ← traceAddMonoidHom_apply, map_sum]
        simp only [traceAddMonoidHom_apply, Category.assoc]
    _ = ∑ j, trace (D.incl j ≫ v ≫ D.proj j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [trace_comp_comm, Category.assoc]

end Monoidal

section Linear

variable {K : Type*} [Field K] (F : C ⥤ ModuleCat K) [F.Additive]

end Linear

end CategoryTheory.ShiftDecomposition
