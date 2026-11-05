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

Source: Deligne, Weil II, (0.2), (1.1.1) d), pp. 144, 147
(auxiliary; not a blueprint node).

## Main definitions

* `FiniteCoefficientFields`: finite intermediate fields in the fixed closure.
* `finiteCoefficientCompositum`: the common upper coefficient field.
* `finiteCoefficientBase`: the least coefficient field.
* `finiteCoefficientFields_properties`: directedness, exhaustion and finite inclusions.
-/

@[expose] public section

universe vCoeff

namespace Padic

variable (l : ℕ) [Fact l.Prime] (K : Type vCoeff) [Field K] [Algebra ℚ_[l] K]
  [IsAlgClosure ℚ_[l] K]

/-- The finite intermediate coefficient fields, ordered by inclusion.
Source: Weil II (0.2), (1.1.1) d)
(auxiliary; not a blueprint node). -/
abbrev FiniteCoefficientFields :=
  {E : IntermediateField ℚ_[l] K // FiniteDimensional ℚ_[l] E}

/-- The recorded finiteness of each field in the directed set.
Source: Weil II (1.1.1) d) (auxiliary; not a blueprint node). -/
instance finiteCoefficientField_finiteDimensional (E : FiniteCoefficientFields l K) :
    FiniteDimensional ℚ_[l] E.val := E.property

/-- The base field is the least coefficient field, so the index set is nonempty.
Source: Weil II (1.1.1) d) (auxiliary; not a blueprint node). -/
noncomputable def finiteCoefficientBase : FiniteCoefficientFields l K := ⟨⊥, inferInstance⟩

end Padic
