/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

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
with respect to the exact pairing between `V` and `Vᘁ` (`CategoryTheory.categoricalTrace`), that
is `CategoryTheory.MonoidalCategory.trace`. By
the invariance under the choice of the pairing it does not depend on the right dual
(`CategoryTheory.categoricalTrace_congr`). For `C` the category of finite-dimensional vector
spaces over a field `Λ`, the ring `End (𝟙_ C)` is `Λ` and this is the usual trace of a linear map.

## Main definitions

- `CategoryTheory.ExactPairing.trace`: the trace with respect to a perfect pairing.
- `CategoryTheory.categoricalTrace`: the categorical trace `Tr(T) ∈ End (𝟙_ C)` of an
  endomorphism of an object with a right dual.

## Main results

- `CategoryTheory.ExactPairing.trace_eq`: the trace does not depend on the perfect pairing.
- `CategoryTheory.categoricalTrace_conj`: the categorical trace is invariant under conjugation by
  an isomorphism `V ≅ W`.
- `CategoryTheory.categoricalTrace_id_tensorUnit`: the identity of the monoidal unit has trace `1`.
- `CategoryTheory.categoricalTrace_eq_zero_of_isZero`: an endomorphism of a zero object has
  trace `0`.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

namespace ExactPairing

/-- The trace `η ≫ (T ▷ W) ≫ β ≫ ε : 𝟙_ C ⟶ 𝟙_ C` of an endomorphism `T` of `V` with respect to
a perfect pairing between `V` and `W`. For the pairing between `V` and a right dual `Vᘁ` this is
`CategoryTheory.MonoidalCategory.trace`
(`CategoryTheory.MonoidalCategory.trace_eq_of_exactPairing`); here the pairing is given by the
object `W` rather than by a `HasRightDual` instance. -/
def trace (V W : C) [ExactPairing V W] (T : V ⟶ V) : End (𝟙_ C) :=
  η_ V W ≫ T ▷ W ≫ (β_ V W).hom ≫ ε_ V W

/-- The trace does not depend on the choice of the perfect pairing. -/
theorem trace_eq (V W W' : C) [ExactPairing V W] [ExactPairing V W'] (T : V ⟶ V) :
    trace V W T = trace V W' T :=
  letI : HasRightDual V := ⟨W⟩
  (MonoidalCategory.trace_eq_of_exactPairing W T).symm.trans
    (MonoidalCategory.trace_eq_of_exactPairing W' T)

end ExactPairing

/-- The categorical trace of an endomorphism `T` of an object `V` with a right dual `Vᘁ`: the
trace `CategoryTheory.MonoidalCategory.trace` of `T`, that is the trace of `T` with respect to the
exact pairing between `V` and `Vᘁ`. -/
noncomputable def categoricalTrace {V : C} [HasRightDual V] (T : V ⟶ V) : End (𝟙_ C) :=
  MonoidalCategory.trace T

lemma categoricalTrace_eq_trace {V : C} [HasRightDual V] (T : V ⟶ V) :
    categoricalTrace T = ExactPairing.trace V Vᘁ T :=
  rfl

/-- The categorical trace does not depend on the choice of the right dual. -/
theorem categoricalTrace_congr {V : C} (h h' : HasRightDual V) (T : V ⟶ V) :
    @categoricalTrace _ _ _ _ _ h T = @categoricalTrace _ _ _ _ _ h' T :=
  letI := h.exact
  letI := h'.exact
  ExactPairing.trace_eq V h.rightDual h'.rightDual T

/-- The categorical trace is invariant under conjugation by an isomorphism. -/
theorem categoricalTrace_conj {V W : C} [HasRightDual V] [HasRightDual W] (e : V ≅ W)
    (T : V ⟶ V) : categoricalTrace (e.inv ≫ T ≫ e.hom) = categoricalTrace T :=
  (trace_eq_of_iso e T _ (by simp)).symm

/-- The identity of the monoidal unit has trace `1`. -/
theorem categoricalTrace_id_tensorUnit [HasRightDual (𝟙_ C)] :
    categoricalTrace (𝟙 (𝟙_ C)) = 1 :=
  trace_id_tensorUnit

/-- An endomorphism of a zero object has trace `0`: the evaluation `Vᘁ ⊗ V ⟶ 𝟙_ C` corresponds to
a morphism out of `V`, so it is zero. -/
theorem categoricalTrace_eq_zero_of_isZero [Preadditive C] {V : C} [HasRightDual V]
    (hV : Limits.IsZero V) (T : V ⟶ V) : categoricalTrace T = 0 := by
  have : ε_ V Vᘁ = 0 := (tensorLeftHomEquiv V V Vᘁ (𝟙_ C)).injective (hV.eq_of_src _ _)
  simp [categoricalTrace, MonoidalCategory.trace, this]

end CategoryTheory
