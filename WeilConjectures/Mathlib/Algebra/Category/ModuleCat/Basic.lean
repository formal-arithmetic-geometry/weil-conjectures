/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# The forget functor on modules is corepresentable

The forget functor `ModuleCat.{u} R ⥤ Type u` is corepresented by `R`, viewed as a
module over itself: a linear map `R →ₗ[R] M` is determined by the image of `1`
(`LinearMap.ringLmapEquivSelf`).

This is the analogue for `ModuleCat` of `Mathlib.Algebra.Category.Grp.ForgetCorepresentable`;
this file imports both `Mathlib.Algebra.Category.ModuleCat.Basic` and
`Mathlib.CategoryTheory.Yoneda` since neither imports the other.

Combined with the instance that corepresentable functors preserve limits of arbitrary
size (`Mathlib.CategoryTheory.Limits.Yoneda`), this shows that the forget functor
preserves limits indexed by arbitrarily large categories, which is needed for sheaf
theory on large sites such as the small étale site of a scheme.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace ModuleCat

variable (R : Type u) [Ring R]

/-- The forget functor `ModuleCat.{u} R ⥤ Type u` is corepresented by `R`,
viewed as a module over itself. -/
def coyonedaObjIsoForget :
    coyoneda.obj (op (ModuleCat.of R R)) ≅ forget (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun M ↦ (ConcreteCategory.homEquiv.trans
      (LinearMap.ringLmapEquivSelf R ℕ M).toEquiv).toIso)

instance forget_isCorepresentable :
    (forget (ModuleCat.{u} R)).IsCorepresentable :=
  Functor.IsCorepresentable.mk' (coyonedaObjIsoForget R)

end ModuleCat
