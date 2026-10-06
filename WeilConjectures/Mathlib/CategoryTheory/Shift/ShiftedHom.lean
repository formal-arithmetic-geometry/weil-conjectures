/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# Linear equivalences of shifted morphisms

In an `R`-linear category `C` with a shift, the types `ShiftedHom X Y m` are `R`-modules. This
file gives the `R`-linear versions of two identifications:

- `CategoryTheory.ShiftedHom.homLinearEquiv`: `(X ⟶ Y) ≃ₗ[R] ShiftedHom X Y m₀` for `m₀ = 0`,
  the linear version of `CategoryTheory.ShiftedHom.homEquiv`;
- `CategoryTheory.ShiftedHom.shiftLinearEquiv`: `ShiftedHom X (Y⟦n⟧) i ≃ₗ[R] ShiftedHom X Y m`
  for `n + i = m`.
-/

@[expose] public section

namespace CategoryTheory.ShiftedHom

variable (R : Type*) [Ring R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
  {M : Type*} [AddMonoid M] [HasShift C M]

/-- The `R`-linear bijection `(X ⟶ Y) ≃ₗ[R] ShiftedHom X Y m₀` when `m₀ = 0`, the linear
version of `CategoryTheory.ShiftedHom.homEquiv`:
```
X ⟶ Y ≅ Y⟦m₀⟧
```
As for `CategoryTheory.ShiftedHom.homEquiv`, the degree is a variable `m₀` with
`m₀ = 0` rather than `0` itself, so that it applies to degrees which are only propositionally
zero, such as the coercion of `0 : ℕ` to `ℤ`. -/
noncomputable def homLinearEquiv (X Y : C) (m₀ : M) (hm₀ : m₀ = 0) :
    (X ⟶ Y) ≃ₗ[R] ShiftedHom X Y m₀ :=
  { homEquiv m₀ hm₀ with
    map_add' := mk₀_add m₀ hm₀
    map_smul' := fun r _ ↦ mk₀_smul m₀ hm₀ r }

@[simp]
lemma homLinearEquiv_apply (X Y : C) (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) :
    homLinearEquiv R X Y m₀ hm₀ f = mk₀ m₀ hm₀ f :=
  rfl

@[simp]
lemma homLinearEquiv_symm_apply (X Y : C) (m₀ : M) (hm₀ : m₀ = 0) (g : ShiftedHom X Y m₀) :
    (homLinearEquiv R X Y m₀ hm₀).symm g = g ≫ (shiftFunctorZero' C m₀ hm₀).hom.app Y :=
  rfl

/-- The shifted morphisms of degree `i` into `Y⟦n⟧` are the shifted morphisms of degree `m` into
`Y`, for `n + i = m`, through `shiftFunctorAdd'`:
```
X ⟶ (Y⟦n⟧)⟦i⟧ ≅ Y⟦m⟧
```
-/
@[simps]
noncomputable def shiftLinearEquiv (X Y : C) (n i m : M) (h : n + i = m) :
    ShiftedHom X (Y⟦n⟧) i ≃ₗ[R] ShiftedHom X Y m where
  toFun f := f ≫ (shiftFunctorAdd' C n i m h).inv.app Y
  invFun g := g ≫ (shiftFunctorAdd' C n i m h).hom.app Y
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := by simp
  map_smul' r f := by simp

end CategoryTheory.ShiftedHom
