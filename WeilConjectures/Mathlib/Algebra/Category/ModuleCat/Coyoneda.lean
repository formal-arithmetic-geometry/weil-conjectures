/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# The ring corepresents the underlying abelian group of a module

For a ring `R`, a morphism `R ⟶ M` of `R`-modules is determined by the image of `1`, so that the
functor `M ↦ Hom(R, M)` to abelian groups is the forgetful functor
(`ModuleCat.preadditiveCoyonedaObjSelfIso`).
-/

@[expose] public section

universe v

open CategoryTheory Opposite

namespace ModuleCat

variable (R : Type v) [Ring R]

/-- Morphisms `R ⟶ M` of `R`-modules are the elements of `M`, by evaluation at `1`. -/
def selfHomAddEquiv (M : ModuleCat.{v} R) : (ModuleCat.of R R ⟶ M) ≃+ M where
  toFun f := f.hom 1
  invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)
  left_inv f := by
    ext
    simp
  right_inv x := by simp
  map_add' _ _ := rfl

/-- The functor `M ↦ Hom(R, M)` from `R`-modules to abelian groups is the forgetful functor. -/
def preadditiveCoyonedaObjSelfIso :
    preadditiveCoyoneda.obj (op (ModuleCat.of R R)) ≅ forget₂ (ModuleCat.{v} R) AddCommGrpCat :=
  NatIso.ofComponents (fun M ↦ (selfHomAddEquiv R M).toAddCommGrpIso)
    (fun g ↦ by
      ext f
      rfl)

end ModuleCat
