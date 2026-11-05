/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Perfectness of a pairing built from a projection map

Let `D` be a monoidal closed category with a shift by `ℤ`, let `R` be an object of `D`, and let
`π : R ⊗ - ⟶ P ⋙ F` be a natural transformation, for functors `P : D ⥤ C` and `F : C ⥤ D`
commuting with shifts. Given `M : D`, maps `c : P M ⟶ V`, `w : V ⟶ W` in `C` and a "trace"
`t : F(W[n]) ⟶ 𝟙_ D`, the composite
```
R ⊗ M[n] ≅ (R ⊗ M)[n] ──π[n]──▶ (F (P M))[n] ──F(c ≫ w)[n]──▶ (F W)[n] ≅ F(W[n]) ──t──▶ 𝟙_ D
```
is a pairing `R ⊗ M[n] ⟶ 𝟙_ D`. This file shows that it is *perfect* — its adjoint
`M[n] ⟶ [R, 𝟙_ D]` is an isomorphism — as soon as `π` is an isomorphism on a class of test
objects detecting isomorphisms, `h ↦ P h ≫ c ≫ w` is a bijection `(N ⟶ M) ≃ (P N ⟶ W)` and
`z ↦ F(z[n]) ≫ t` is a bijection `(U ⟶ W) ≃ (F(U[n]) ⟶ 𝟙_ D)`
(`CategoryTheory.MonoidalClosed.isIso_curry_of_projection`).

This is the formal core of the statement that the derived Poincaré pairing is perfect: there
`π` is the projection map of `Ra_!`, `P = La^* ⋙ (K ⊗ᴸ -)`, `c` is induced by the counit of
`La^* ⊣ Ra_*`, `w` is the evaluation, and `t` is the trace of `Ra_! ⊣ Ra^!` read through an
orientation.

## Implementation notes

The instances on `C` and `D` are taken as implicit arguments rather than instance arguments, so
that applying the theorem to a concrete pairing determines them by unification with that
pairing. This keeps the instances that the kernel has to compare syntactically equal.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

open Category MonoidalCategory

variable {C D : Type*} [Category C] [Category D]

end CategoryTheory.MonoidalClosed
