/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!

# Categorical traces and supertraces

Let `C` be a braided monoidal preadditive category. The *categorical trace* of an endomorphism
`T : V ⟶ V` of an object `V` with a right dual `Vᘁ` is the endomorphism of the monoidal unit
```
𝟙_ C --η--> V ⊗ Vᘁ --T ▷ Vᘁ--> V ⊗ Vᘁ --β--> Vᘁ ⊗ V --ε--> 𝟙_ C,
```
an element of the ring `End (𝟙_ C)` (`CategoryTheory.categoricalTrace`). For `C` the category of
finite-dimensional vector spaces over a field `Λ`, the ring `End (𝟙_ C)` is `Λ` and this is the
usual trace of a linear map.

Whether `V` is dualizable is a property, but a right dual is data. The trace is therefore defined
using a right dual chosen from the proposition `Nonempty (HasRightDual V)`, and is `0` when `V`
has no right dual. The trace computed with any other right dual is the same, duals being unique up
to unique isomorphism; this is the content of the invariance under conjugation below.

The *supertrace* of a family of endomorphisms `T i : V i ⟶ V i` indexed by `i : ℤ` is the
alternating sum `∑ᶠ i, (-1)ⁱ Tr(T i)` (`CategoryTheory.superTrace`). For the cohomology
`V i = Hⁱ(W)` of a perfect complex `W` with an endomorphism, this is the supertrace
`STr(T | W) = ∑ᵢ (-1)ⁱ Tr(Hⁱ(T) | Hⁱ(W))` of the trace formula. The sum is a `finsum`: it is `0`
unless only finitely many traces are nonzero, which holds for the bounded complexes to which it is
applied.

## Main definitions

- `CategoryTheory.categoricalTrace`: the categorical trace `Tr(T) ∈ End (𝟙_ C)`.
- `CategoryTheory.superTrace`: the alternating sum of the traces of a `ℤ`-indexed family.

## Sorried input

- `CategoryTheory.categoricalTrace_conj`: the trace is invariant under conjugation by an
  isomorphism `V ≅ W`. The right duals chosen for `V` and `W` are unrelated, so this rests on the
  uniqueness of duals up to unique isomorphism.
- `CategoryTheory.categoricalTrace_id_tensorUnit`: the identity of the monoidal unit has trace `1`.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]

/-- The categorical trace `η ≫ (T ▷ Vᘁ) ≫ β ≫ ε : 𝟙_ C ⟶ 𝟙_ C` of an endomorphism `T` of an object
`V`, computed with a right dual `Vᘁ` chosen from `Nonempty (HasRightDual V)`; it is `0` when `V`
has no right dual. -/
noncomputable def categoricalTrace {V : C} (T : V ⟶ V) : End (𝟙_ C) :=
  open Classical in
  if h : Nonempty (HasRightDual V) then
    letI := h.some
    η_ V Vᘁ ≫ T ▷ Vᘁ ≫ (β_ V Vᘁ).hom ≫ ε_ V Vᘁ
  else 0

/-- The supertrace `∑ᶠ i, (-1)ⁱ Tr(T i)` of a `ℤ`-indexed family of endomorphisms. -/
noncomputable def superTrace (V : ℤ → C) (T : ∀ i, V i ⟶ V i) : End (𝟙_ C) :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • categoricalTrace (T i)

/-- The categorical trace is invariant under conjugation by an isomorphism. -/
theorem categoricalTrace_conj {V W : C} (e : V ≅ W) (T : V ⟶ V) :
    categoricalTrace (e.inv ≫ T ≫ e.hom) = categoricalTrace T :=
  sorry

/-- The identity of the monoidal unit has trace `1`. -/
theorem categoricalTrace_id_tensorUnit : categoricalTrace (𝟙 (𝟙_ C)) = 1 :=
  sorry

end CategoryTheory
