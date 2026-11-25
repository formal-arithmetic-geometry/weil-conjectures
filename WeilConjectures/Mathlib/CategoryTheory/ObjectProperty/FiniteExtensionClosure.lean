/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosureShift
public import Mathlib.CategoryTheory.Triangulated.Generators

/-! # Finite extension presentations of thick envelopes

Every object of the thick envelope of a nonempty property `P` of a triangulated category is a
retract of an iterated extension of shifts of objects of `P`.

## References

* [Stacks, Tags 0FX1 and 0FX2]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped ZeroObject

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Every object of the thick envelope of a nonempty property `P` is a retract of an object
of some iterated extension product of the shift closure of `P`. -/
theorem triangEnvelope_le_finiteExtensions (P : ObjectProperty C) [P.Nonempty] :
    P.triangEnvelope ≤ fun K ↦ ∃ n : ℕ,
      ((P.shiftClosure ℤ).extensionProductIter n).retractClosure K := by
  let S := P.shiftClosure ℤ
  let Q : ObjectProperty C := fun K ↦ ∃ n : ℕ, (S.extensionProductIter n).retractClosure K
  have hP : P ≤ Q := fun K hK ↦
    ⟨0, le_retractClosure _ K ((le_shiftClosure P) K hK)⟩
  have : Q.IsStableUnderRetracts := ⟨fun r ⟨n, hn⟩ ↦
    ⟨n, (S.extensionProductIter n).retractClosure.prop_of_retract r hn⟩⟩
  have : Q.IsStableUnderShift ℤ :=
    ⟨fun a ↦ IsStableUnderShiftBy.mk (fun K ⟨n, hn⟩ ↦
      ⟨n, IsStableUnderShiftBy.le_shift K hn⟩)⟩
  have : Q.IsTriangulatedClosed₂ := IsTriangulatedClosed₂.mk' (by
    intro T hT h₁ h₃
    obtain ⟨p, hp⟩ := h₁
    obtain ⟨q, hq⟩ := h₃
    refine ⟨(p + 1) + q, ?_⟩
    rw [extensionProductIter_add S rfl]
    exact extensionProduct_retractClosure_retractClosure_le _ _ _
      ⟨_, _, _, _, _, hT, hp, hq⟩)
  have hQ : Q P.arbitrary := hP _ P.prop_arbitrary
  have : Q.ContainsZero := ⟨⟨0, isZero_zero C,
    Q.ext_of_isTriangulatedClosed₂ _
      (rot_of_distTriang _ (contractible_distinguished P.arbitrary))
      hQ (Q.le_shift _ _ hQ)⟩⟩
  have : Q.IsTriangulated := {}
  exact (triangEnvelope_le_iff P).mpr hP

end CategoryTheory.ObjectProperty
