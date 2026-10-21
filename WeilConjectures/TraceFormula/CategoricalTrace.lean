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
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!

# Categorical traces and supertraces

Let `C` be a braided monoidal preadditive category. The *categorical trace* of an endomorphism
`T : V ⟶ V` of an object `V` with a right dual `Vᘁ` is the endomorphism of the monoidal unit
```
𝟙_ C --η--> V ⊗ Vᘁ --T ▷ Vᘁ--> V ⊗ Vᘁ --β--> Vᘁ ⊗ V --ε--> 𝟙_ C,
```
an element of the ring `End (𝟙_ C)`. For `C` the category of finite-dimensional vector spaces
over a field `Λ`, the ring `End (𝟙_ C)` is `Λ` and this is the usual trace of a linear map.

This is `CategoryTheory.MonoidalCategory.trace`, which takes the right dual as an instance.
Whether `V` is dualizable is a property, but a right dual is data, so
`CategoryTheory.categoricalTrace` computes `trace` with a right dual chosen from the proposition
`Nonempty (HasRightDual V)`, and is `0` when `V` has no right dual. The trace does not depend on
the chosen right dual (`CategoryTheory.categoricalTrace_eq_trace`).

The *supertrace* of a family of endomorphisms `T i : V i ⟶ V i` indexed by `i : ℤ` is the
alternating sum `∑ᶠ i, (-1)ⁱ Tr(T i)` (`CategoryTheory.superTrace`). For the cohomology
`V i = Hⁱ(W)` of a perfect complex `W` with an endomorphism, this is the supertrace
`STr(T | W) = ∑ᵢ (-1)ⁱ Tr(Hⁱ(T) | Hⁱ(W))` of the trace formula. The sum is a `finsum`: it is `0`
unless only finitely many traces are nonzero, which holds for the bounded complexes to which it is
applied.

## Main definitions

- `CategoryTheory.categoricalTrace`: the categorical trace `Tr(T) ∈ End (𝟙_ C)`, or `0` if `V`
  has no right dual.
- `CategoryTheory.superTrace`: the alternating sum of the traces of a `ℤ`-indexed family.

## Main results

- `CategoryTheory.categoricalTrace_eq_trace`: for any right dual of `V`, `categoricalTrace` is
  `trace`.
- `CategoryTheory.categoricalTrace_conj`: the trace is invariant under conjugation by an
  isomorphism `V ≅ W`.
- `CategoryTheory.categoricalTrace_eq_zero_of_isZero`: an endomorphism of a zero object has
  trace `0`.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]

/-- The categorical trace `η ≫ (T ▷ Vᘁ) ≫ β ≫ ε : 𝟙_ C ⟶ 𝟙_ C` of an endomorphism `T` of an object
`V` (`CategoryTheory.MonoidalCategory.trace`), computed with a right dual `Vᘁ` chosen from
`Nonempty (HasRightDual V)`; it is `0` when `V` has no right dual. -/
noncomputable def categoricalTrace {V : C} (T : V ⟶ V) : End (𝟙_ C) :=
  open Classical in
  if h : Nonempty (HasRightDual V) then
    letI := h.some
    trace T
  else 0

/-- The supertrace `∑ᶠ i, (-1)ⁱ Tr(T i)` of a `ℤ`-indexed family of endomorphisms. -/
noncomputable def superTrace (V : ℤ → C) (T : ∀ i, V i ⟶ V i) : End (𝟙_ C) :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • categoricalTrace (T i)

/-- For any right dual of `V`, the categorical trace is the trace computed with that dual. -/
theorem categoricalTrace_eq_trace {V : C} [d : HasRightDual V] (T : V ⟶ V) :
    categoricalTrace T = trace T := by
  have h : Nonempty (HasRightDual V) := ⟨d⟩
  rw [categoricalTrace, dif_pos h]
  exact @trace_eq_of_iso _ _ _ _ _ _ h.some d (Iso.refl V) T T (by simp)

/-- The categorical trace is invariant under conjugation by an isomorphism. -/
theorem categoricalTrace_conj {V W : C} (e : V ≅ W) (T : V ⟶ V) :
    categoricalTrace (e.inv ≫ T ≫ e.hom) = categoricalTrace T := by
  by_cases hV : Nonempty (HasRightDual V)
  · obtain ⟨dV⟩ := hV
    let : HasRightDual W := @HasRightDual.mk _ _ _ _ Vᘁ (exactPairingCongrLeft e.symm)
    rw [categoricalTrace_eq_trace, categoricalTrace_eq_trace]
    exact (trace_eq_of_iso e T _ (by simp)).symm
  · have hW : ¬ Nonempty (HasRightDual W) := fun ⟨dW⟩ ↦
      hV ⟨@HasRightDual.mk _ _ _ _ Wᘁ (exactPairingCongrLeft e)⟩
    rw [categoricalTrace, categoricalTrace, dif_neg hV, dif_neg hW]

/-- The identity of the monoidal unit has trace `1`. -/
theorem categoricalTrace_id_tensorUnit : categoricalTrace (𝟙 (𝟙_ C)) = 1 := by
  let : HasRightDual (𝟙_ C) := ⟨𝟙_ C⟩
  rw [categoricalTrace_eq_trace, trace_id_tensorUnit]
  rfl

/-- An endomorphism of a zero object has trace `0`: the evaluation `Vᘁ ⊗ V ⟶ 𝟙_ C` corresponds to
a morphism out of `V`, so it is zero. -/
theorem categoricalTrace_eq_zero_of_isZero {V : C} (hV : Limits.IsZero V) (T : V ⟶ V) :
    categoricalTrace T = 0 := by
  rw [categoricalTrace]
  split_ifs with h
  · let := h.some
    have : ε_ V Vᘁ = 0 := (tensorLeftHomEquiv V V Vᘁ (𝟙_ C)).injective (hV.eq_of_src _ _)
    simp [trace, this]
  · rfl

end CategoryTheory
