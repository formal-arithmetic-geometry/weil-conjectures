/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The categorical trace

In a braided monoidal category, an object `X` with a right dual `Xᘁ` has an
`ExactPairing X Xᘁ`, hence a coevaluation `𝟙_ C ⟶ X ⊗ Xᘁ` and an evaluation
`Xᘁ ⊗ X ⟶ 𝟙_ C`. The *trace* of an endomorphism `f : X ⟶ X` is the resulting
endomorphism of the unit object.

This is the categorical trace used by the Lefschetz trace formula: for
`C = Perf(R) ⊆ D(R)` it is the usual trace of an endomorphism of a perfect complex,
and `End (𝟙_ C) = R`.

## Main definitions

- `CategoryTheory.MonoidalCategory.trace`: the trace of an endomorphism of a dualizable
  object.

## Implementation notes

In a merely braided category the two ways of turning `X ⊗ Xᘁ` into `Xᘁ ⊗ X` differ, and
`trace` uses `(β_ X Xᘁ).hom`. In the symmetric case, which is the one the trace formula
uses, the two agree.
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

/-- The trace of an endomorphism `f : X ⟶ X` of an object with a right dual `Xᘁ` is the
composite

```
       η_ X Xᘁ        f ▷ Xᘁ        β_ X Xᘁ        ε_ X Xᘁ
  𝟙_ C ──────→ X ⊗ Xᘁ ──────→ X ⊗ Xᘁ ──────→ Xᘁ ⊗ X ──────→ 𝟙_ C
```

of the coevaluation, `f ⊗ 𝟙`, the braiding and the evaluation. For the symmetric monoidal
category `(Perf R, ⊗ᴸ_R, R)` of perfect complexes over a commutative ring `R` this is
`tr_R(f | P)`, an element of `End (𝟙_ C) = R`
(blueprint: `sk-d-trace`). -/
noncomputable def trace {X : C} [HasRightDual X] (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ

end CategoryTheory.MonoidalCategory
