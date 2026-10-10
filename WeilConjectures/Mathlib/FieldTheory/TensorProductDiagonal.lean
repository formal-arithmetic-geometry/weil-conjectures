/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# The diagonal of `E ⊗_F E` for an algebraic extension

Let `E/F` be an algebraic field extension. The kernel of the multiplication map
`E ⊗_F E → E` dies in `E ⊗_L E` for some intermediate field `L` finite over `F`: the kernel is
spanned by the elements `1 ⊗ s - s ⊗ 1`, and finitely many `s` lie in a finite subextension.
Equivalently, `E` is the filtered colimit of the rings `E ⊗_L E` over the finite subextensions
`L`, so that `Spec E` is the limit of the schemes `Spec (E ⊗_L E)`, with `Spec E` embedded
diagonally.

## Main statements

- `IntermediateField.exists_finiteDimensional_mapOfCompatibleSMul_eq_zero`
-/

@[expose] public section

open TensorProduct

namespace IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- For `s ∈ L`, the elements `1 ⊗ s` and `s ⊗ 1` of `E ⊗_L E` agree. -/
lemma one_tmul_eq_tmul_one (L : IntermediateField F E) {s : E} (hs : s ∈ L) :
    (1 : E) ⊗ₜ[L] s = s ⊗ₜ[L] (1 : E) := by
  have h : s = (⟨s, hs⟩ : L) • (1 : E) := by
    rw [Algebra.smul_def, mul_one]
    rfl
  rw [h, smul_tmul]

/-- **The kernel of multiplication dies at a finite level.** Let `E/F` be algebraic and let
`x ∈ E ⊗_F E` be killed by the multiplication map `E ⊗_F E → E`. Then the image of `x` in
`E ⊗_L E` vanishes for some intermediate field `L` which is finite over `F`. -/
theorem exists_finiteDimensional_mapOfCompatibleSMul_eq_zero [Algebra.IsAlgebraic F E]
    (x : E ⊗[F] E) (hx : Algebra.TensorProduct.lmul' F x = 0) :
    ∃ L : IntermediateField F E, FiniteDimensional F L ∧
      mapOfCompatibleSMul L F E E E x = 0 := by
  have hmem : x ∈ (KaehlerDifferential.ideal F E).restrictScalars E := by
    change x ∈ RingHom.ker (Algebra.TensorProduct.lmul' F (S := E))
    exact hx
  rw [← KaehlerDifferential.submodule_span_range_eq_ideal,
    Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨c, rfl⟩ := hmem
  let L := IntermediateField.adjoin F (c.support : Set E)
  have hL : FiniteDimensional F L :=
    IntermediateField.finiteDimensional_adjoin fun s _ ↦ Algebra.IsIntegral.isIntegral s
  refine ⟨L, hL, ?_⟩
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun s hs ↦ ?_
  rw [map_smul, map_sub, mapOfCompatibleSMul_tmul, mapOfCompatibleSMul_tmul,
    one_tmul_eq_tmul_one L (IntermediateField.subset_adjoin F _ hs), sub_self, smul_zero]

end IntermediateField
