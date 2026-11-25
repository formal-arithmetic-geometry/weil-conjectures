/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Finite coefficient fields inside an algebraic closure

We consider the directed system of finite extensions of `ℚ_[l]` inside a fixed algebraic
closure.

## Main definitions

* `FiniteCoefficientFields`: finite intermediate fields in the fixed closure.
* `finiteCoefficientCompositum`: the common upper coefficient field.
* `finiteCoefficientBase`: the least coefficient field.
* `finiteCoefficientFields_properties`: directedness, exhaustion and finite inclusions.

## References

* Deligne, *La conjecture de Weil II*, (0.2), (1.1.1) d), pp. 144, 147.
-/

@[expose] public section

universe vCoeff

namespace Padic

variable (l : ℕ) [Fact l.Prime] (K : Type vCoeff) [Field K] [Algebra ℚ_[l] K]
  [IsAlgClosure ℚ_[l] K]

/-- The finite intermediate coefficient fields, ordered by inclusion. -/
abbrev FiniteCoefficientFields :=
  {E : IntermediateField ℚ_[l] K // FiniteDimensional ℚ_[l] E}

/-- The recorded finiteness of each field in the directed set. -/
instance finiteCoefficientField_finiteDimensional (E : FiniteCoefficientFields l K) :
    FiniteDimensional ℚ_[l] E.val := E.property

/-- The compositum is the supremum of the underlying intermediate fields. -/
noncomputable def finiteCoefficientCompositum (E F : FiniteCoefficientFields l K) :
    FiniteCoefficientFields l K :=
  ⟨E.val ⊔ F.val, inferInstance⟩

/-- The base field is the least coefficient field, so the index set is nonempty. -/
noncomputable def finiteCoefficientBase : FiniteCoefficientFields l K := ⟨⊥, inferInstance⟩

/-- The coefficient fields are directed, exhaust the algebraic closure, and inclusions
are finite extensions. -/
theorem finiteCoefficientFields_properties :
    (∀ E F : FiniteCoefficientFields l K,
      E ≤ finiteCoefficientCompositum l K E F ∧ F ≤ finiteCoefficientCompositum l K E F) ∧
    (∀ x : K, ∃ E : FiniteCoefficientFields l K, x ∈ E.val) ∧
    (∀ E L : FiniteCoefficientFields l K, ∀ h : E ≤ L,
      letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
      FiniteDimensional E.val L.val) := by
  refine ⟨?_, ?_, ?_⟩
  · intro E F
    exact ⟨show E.val ≤ E.val ⊔ F.val from le_sup_left,
      show F.val ≤ E.val ⊔ F.val from le_sup_right⟩
  · intro x
    refine ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩, ?_⟩
    exact IntermediateField.subset_adjoin ℚ_[l] {x} (Set.mem_singleton x)
  · intro E L h
    let := (IntermediateField.inclusion h).toRingHom.toAlgebra
    have : IsScalarTower ℚ_[l] E.val L.val :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact Module.Finite.of_restrictScalars_finite ℚ_[l] E.val L.val

end Padic
