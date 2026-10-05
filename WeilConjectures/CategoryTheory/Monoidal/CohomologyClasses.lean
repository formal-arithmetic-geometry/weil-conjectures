/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Shift.Basic

/-!
# Cohomology classes in a monoidal category with a shift

In a monoidal category `C` with a shift by `ℤ`, a *cohomology class of degree `i`* of an
object `M` is a morphism `𝟙_ C ⟶ M⟦i⟧` out of the unit. This is the convention of
`WeilConjectures.SixFunctors.Etale.Derived.Supports`: in the derived category `D(T_ét, Λ)` of
étale sheaves the unit is the constant complex `Λ_T`, and the classes of degree `i` of `M` are
the hypercohomology `H^i(T, M)`. In a `R`-linear category the classes form an `R`-module.

## Main definitions

- `CategoryTheory.cohomologyClasses M i`: the classes `𝟙_ C ⟶ M⟦i⟧`.
- `CategoryTheory.cohomologyClassesShiftEquiv`: the classes of degree `i` of `M⟦n⟧` are the
  classes of degree `n + i` of `M`.
- `CategoryTheory.cohomologyClassesZeroEquiv`: the classes of degree `0` of `M` are the
  morphisms `𝟙_ C ⟶ M`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C] [HasShift C ℤ]

/-- The *cohomology classes of degree `i`* of an object `M` of a monoidal category with a
shift: the morphisms `𝟙_ C ⟶ M⟦i⟧` out of the unit. This is `CategoryTheory.ShiftedHom` with
source `𝟙_ C`, written as a plain type of morphisms so that classes compose with `≫`. -/
abbrev cohomologyClasses (M : C) (i : ℤ) : Type _ :=
  𝟙_ C ⟶ M⟦i⟧

variable (R : Type*) [Semiring R] [Preadditive C] [Linear R C]

/-- The classes of degree `i` of `M⟦n⟧` are the classes of degree `m = n + i` of `M`, through
`(M⟦n⟧)⟦i⟧ ≅ M⟦m⟧`. -/
noncomputable def cohomologyClassesShiftEquiv (M : C) (n i m : ℤ) (h : n + i = m) :
    cohomologyClasses (M⟦n⟧) i ≃ₗ[R] cohomologyClasses M m :=
  Linear.homCongr R (Iso.refl _) ((shiftFunctorAdd' C n i m h).app M).symm

/-- The classes of degree `n = 0` of `M` are the morphisms `𝟙_ C ⟶ M`, through
`M⟦n⟧ ≅ M`. -/
noncomputable def cohomologyClassesZeroEquiv (M : C) (n : ℤ) (h : n = 0) :
    cohomologyClasses M n ≃ₗ[R] (𝟙_ C ⟶ M) :=
  Linear.homCongr R (Iso.refl _) ((shiftFunctorZero' C n h).app M)

end CategoryTheory
