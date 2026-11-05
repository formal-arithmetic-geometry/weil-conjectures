/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Unrotating a strict cone square -/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
open CochainComplex

@[simp] private lemma triangleUnit_hom₁
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] (T : Triangle D) :
    ((shiftFunctorCompIsoId (Triangle D) (1 : ℤ) (-1) (by simp)).hom.app T).hom₁ =
      (shiftFunctorCompIsoId D (1 : ℤ) (-1) (by simp)).hom.app T.obj₁ := by
  simp [shiftFunctorCompIsoId]

@[simp] private lemma triangleUnit_hom₃
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] (T : Triangle D) :
    ((shiftFunctorCompIsoId (Triangle D) (1 : ℤ) (-1) (by simp)).hom.app T).hom₃ =
      (shiftFunctorCompIsoId D (1 : ℤ) (-1) (by simp)).hom.app T.obj₃ := by
  simp [shiftFunctorCompIsoId]

