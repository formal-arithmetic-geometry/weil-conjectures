/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Finite coefficient fields inside an algebraic closure

Source: Deligne, Weil II, (0.2), (1.1.1) d), pp. 144, 147
(blueprint: def-weil-finite-subextension-directed-set).

## Main definitions

* `FiniteCoefficientFields`: finite intermediate fields in the fixed closure.
* `finiteCoefficientCompositum`: the common upper coefficient field.
* `finiteCoefficientBase`: the least coefficient field.
* `finiteCoefficientFields_properties`: directedness, exhaustion and finite inclusions.
-/

universe vCoeff

namespace Padic

variable (l : ℕ) [Fact l.Prime] (K : Type vCoeff) [Field K] [Algebra ℚ_[l] K]
  [IsAlgClosure ℚ_[l] K]

/-- The finite intermediate coefficient fields, ordered by inclusion.
Source: Weil II (0.2), (1.1.1) d)
(blueprint: def-weil-finite-subextension-directed-set). -/
abbrev FiniteCoefficientFields :=
  {E : IntermediateField ℚ_[l] K // FiniteDimensional ℚ_[l] E}

/-- The recorded finiteness of each field in the directed set.
Source: Weil II (1.1.1) d) (blueprint: def-weil-finite-subextension-directed-set). -/
instance finiteCoefficientField_finiteDimensional (E : FiniteCoefficientFields l K) :
    FiniteDimensional ℚ_[l] E.val := E.property

/-- The compositum is the supremum of the underlying intermediate fields.
Finiteness is Mathlib's `IntermediateField.finiteDimensional_sup`.
Source: Weil II (1.1.1) d) (blueprint: def-weil-finite-subextension-directed-set). -/
noncomputable def finiteCoefficientCompositum (E F : FiniteCoefficientFields l K) :
    FiniteCoefficientFields l K :=
  ⟨E.val ⊔ F.val, inferInstance⟩

/-- The base field is the least coefficient field, so the index set is nonempty.
Source: Weil II (1.1.1) d) (blueprint: def-weil-finite-subextension-directed-set). -/
noncomputable def finiteCoefficientBase : FiniteCoefficientFields l K := ⟨⊥, inferInstance⟩

/-- The coefficient fields are directed, exhaust the algebraic closure, and inclusions
are finite extensions.
Source: Weil II (0.2), (1.1.1) d)
(blueprint: def-weil-finite-subextension-directed-set).
Proof: the compositum is an upper bound and is finite-dimensional by
`IntermediateField.finiteDimensional_sup`; the bottom field witnesses nonemptiness.
Every element of the closure is algebraic and hence generates a finite simple extension,
which contains that element. If E is contained in L, a finite spanning set of L over
`ℚ_[l]` also spans over E, since the base scalars embed into E; thus L is finite over E. -/
theorem finiteCoefficientFields_properties :
    (∀ E F : FiniteCoefficientFields l K,
      E ≤ finiteCoefficientCompositum l K E F ∧ F ≤ finiteCoefficientCompositum l K E F) ∧
    (∀ x : K, ∃ E : FiniteCoefficientFields l K, x ∈ E.val) ∧
    (∀ E L : FiniteCoefficientFields l K, ∀ h : E ≤ L,
      letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
      FiniteDimensional E.val L.val) := by
  sorry

end Padic
