/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Field extensions and towers

Source: blueprint `sec-picard-framework/sk-thm-picard-rr/def-pc-field-tower.md`
(blueprint: def-pc-field-tower); Stacks Project, Fields, Tags 09FV, 09GC, 09H1,
09HE, and 09GS.

## Main definitions

* `FieldExtension.degree` is the vector-space degree, with `⊤` for an infinite
  dimensional extension.
The other clauses in the blueprint are recorded by Mathlib's existing notions:
`Module.Finite k K`, `Algebra.IsAlgebraic k K`,
`Module.Finite k K ∧ Algebra.IsSeparable k K`,
`IsPurelyInseparable k K`, and `IsAlgClosure k K`, respectively.
-/

@[expose] public section

universe u v

namespace FieldExtension

end FieldExtension
