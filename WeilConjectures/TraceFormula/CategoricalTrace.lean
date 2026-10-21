/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!

# Categorical traces

Let `C` be a braided monoidal category. The *trace* of an endomorphism `T : V ⟶ V` with respect
to a perfect pairing between `V` and `W`, that is an exact pairing with coevaluation
`η : 𝟙_ C ⟶ V ⊗ W` and evaluation `ε : W ⊗ V ⟶ 𝟙_ C`, is the endomorphism of the monoidal unit
```
𝟙_ C --η--> V ⊗ W --T ▷ W--> V ⊗ W --β--> W ⊗ V --ε--> 𝟙_ C,
```
an element of the ring `End (𝟙_ C)` (`CategoryTheory.ExactPairing.trace`). It does not depend on
the choice of the perfect pairing (`CategoryTheory.ExactPairing.trace_eq`), duals being unique up
to unique isomorphism.

The *categorical trace* of an endomorphism of an object `V` with a right dual `Vᘁ` is the trace
with respect to the exact pairing between `V` and `Vᘁ` (`CategoryTheory.categoricalTrace`). By
the invariance under the choice of the pairing it does not depend on the right dual
(`CategoryTheory.categoricalTrace_congr`). For `C` the category of finite-dimensional vector
spaces over a field `Λ`, the ring `End (𝟙_ C)` is `Λ` and this is the usual trace of a linear map.

## Main definitions

- `CategoryTheory.ExactPairing.trace`: the trace with respect to a perfect pairing.
- `CategoryTheory.categoricalTrace`: the categorical trace `Tr(T) ∈ End (𝟙_ C)` of an
  endomorphism of an object with a right dual.

## Sorried input

- `CategoryTheory.ExactPairing.trace_eq`: the trace does not depend on the perfect pairing. This
  rests on the uniqueness of duals up to unique isomorphism.
- `CategoryTheory.categoricalTrace_conj`: the categorical trace is invariant under conjugation by
  an isomorphism `V ≅ W`.
- `CategoryTheory.categoricalTrace_id_tensorUnit`: the identity of the monoidal unit has trace `1`.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

namespace ExactPairing

/-- The trace `η ≫ (T ▷ W) ≫ β ≫ ε : 𝟙_ C ⟶ 𝟙_ C` of an endomorphism `T` of `V` with respect to
a perfect pairing between `V` and `W`. -/
def trace (V W : C) [ExactPairing V W] (T : V ⟶ V) : End (𝟙_ C) :=
  η_ V W ≫ T ▷ W ≫ (β_ V W).hom ≫ ε_ V W

/-- The trace does not depend on the choice of the perfect pairing. -/
theorem trace_eq (V W W' : C) [ExactPairing V W] [ExactPairing V W'] (T : V ⟶ V) :
    trace V W T = trace V W' T :=
  sorry

end ExactPairing

/-- The categorical trace of an endomorphism `T` of an object `V` with a right dual `Vᘁ`: the
trace of `T` with respect to the exact pairing between `V` and `Vᘁ`. -/
def categoricalTrace {V : C} [HasRightDual V] (T : V ⟶ V) : End (𝟙_ C) :=
  ExactPairing.trace V Vᘁ T

/-- The categorical trace does not depend on the choice of the right dual. -/
theorem categoricalTrace_congr {V : C} (h h' : HasRightDual V) (T : V ⟶ V) :
    @categoricalTrace _ _ _ _ _ h T = @categoricalTrace _ _ _ _ _ h' T :=
  letI := h.exact
  letI := h'.exact
  ExactPairing.trace_eq V h.rightDual h'.rightDual T

/-- The categorical trace is invariant under conjugation by an isomorphism. -/
theorem categoricalTrace_conj {V W : C} [HasRightDual V] [HasRightDual W] (e : V ≅ W)
    (T : V ⟶ V) : categoricalTrace (e.inv ≫ T ≫ e.hom) = categoricalTrace T :=
  sorry

/-- The identity of the monoidal unit has trace `1`. -/
theorem categoricalTrace_id_tensorUnit : categoricalTrace (𝟙 (𝟙_ C)) = 1 :=
  sorry

end CategoryTheory
