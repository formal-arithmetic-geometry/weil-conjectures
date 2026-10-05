/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
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

variable (R : Type*) [Semiring R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
  {M : Type*} [AddMonoid M] [HasShift C M]

/-- The `R`-linear bijection `(X ⟶ Y) ≃ₗ[R] ShiftedHom X Y m₀` when `m₀ = 0`, through
`shiftFunctorZero'`:
```
X ⟶ Y ≅ Y⟦m₀⟧
```
As for `CategoryTheory.ShiftedHom.homEquiv`, the degree is a variable `m₀` with
`m₀ = 0` rather than `0` itself, so that it applies to degrees which are only propositionally
zero, such as the coercion of `0 : ℕ` to `ℤ`. -/
noncomputable def homLinearEquiv (X Y : C) (m₀ : M) (hm₀ : m₀ = 0) :
    (X ⟶ Y) ≃ₗ[R] ShiftedHom X Y m₀ :=
  Linear.homCongr R (Iso.refl _) ((shiftFunctorZero' C m₀ hm₀).app Y).symm

/-- The shifted morphisms of degree `i` into `Y⟦n⟧` are the shifted morphisms of degree `m` into
`Y`, for `n + i = m`, through `shiftFunctorAdd'`:
```
X ⟶ (Y⟦n⟧)⟦i⟧ ≅ Y⟦m⟧
```
-/
noncomputable def shiftLinearEquiv (X Y : C) (n i m : M) (h : n + i = m) :
    ShiftedHom X (Y⟦n⟧) i ≃ₗ[R] ShiftedHom X Y m :=
  Linear.homCongr R (Iso.refl _) ((shiftFunctorAdd' C n i m h).app Y).symm

end CategoryTheory.ShiftedHom
