/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Retracts as cokernels

In a preadditive category, a retract `X` of `Y` is the cokernel of the idempotent endomorphism
`𝟙 Y - r ≫ i` of `Y` (`CategoryTheory.Retract.isoCokernel`).

A retract of a split monomorphism, for instance a morphism isomorphic to it as an arrow, is a
split monomorphism
(`CategoryTheory.RetractArrow.isSplitMono`, `CategoryTheory.Arrow.isSplitMono_of_iso`).
-/

@[expose] public section

namespace CategoryTheory.Retract

open Limits

variable {C : Type*} [Category* C] [Preadditive C] {X Y : C}

/-- A retract `X` of `Y` (with `i : X ⟶ Y`, `r : Y ⟶ X`, `i ≫ r = 𝟙 X`) is the cokernel of the
idempotent endomorphism `𝟙 Y - r ≫ i` of `Y`: the isomorphism is `i ≫ π`, and its inverse
is induced by `r`, which kills `𝟙 Y - r ≫ i`.
```
         𝟙 Y - r ≫ i         π
    Y ─────────────────▶ Y ─────▶ cokernel (𝟙 Y - r ≫ i)
                         │              │
                       r │              │ cokernel.desc r
                         ▼              ▼
                         X ════════════ X
```
-/
noncomputable def isoCokernel (e : Retract X Y) [HasCokernel (𝟙 Y - e.r ≫ e.i)] :
    X ≅ cokernel (𝟙 Y - e.r ≫ e.i) where
  hom := e.i ≫ cokernel.π _
  inv := cokernel.desc _ e.r (by simp [Preadditive.sub_comp])
  hom_inv_id := by simp
  inv_hom_id := by
    ext
    have h := cokernel.condition (𝟙 Y - e.r ≫ e.i)
    rw [Preadditive.sub_comp, sub_eq_zero] at h
    simpa using h.symm

end CategoryTheory.Retract

namespace CategoryTheory.RetractArrow

variable {C : Type*} [Category* C] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}

/-- A retract of a split monomorphism is a split monomorphism: if `f` is a retract of `g`, then
`h.i.right ≫ retraction g ≫ h.r.left` is a retraction of `f`. -/
lemma isSplitMono (h : RetractArrow f g) [IsSplitMono g] : IsSplitMono f :=
  IsSplitMono.mk' ⟨h.i.right ≫ retraction g ≫ h.r.left, by
    rw [← h.i_w_assoc, IsSplitMono.id_assoc, h.retract_left]⟩

end CategoryTheory.RetractArrow

/-- A morphism isomorphic, as an arrow, to a split monomorphism is a split monomorphism. -/
lemma CategoryTheory.Arrow.isSplitMono_of_iso {C : Type*} [Category* C] {X Y X' Y' : C}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk g) [IsSplitMono g] : IsSplitMono f :=
  RetractArrow.isSplitMono (Retract.ofIso e)
