/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.Ring

/-! # Bilinear functors on raw scalar localizations

Source: module base change, Stacks 00CV and 00CX; the rational tensor paragraph of
blueprint `def-weil-derived-pullback-tensor-hom`.
(blueprint: lem-sf-bilinear-functor-scalar-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TensorProduct
namespace CategoryTheory.ScalarLocalization

section TensorLocalization
set_option backward.defeqAttrib.useBackward false
variable {D : Type*} [Category* D] [Preadditive D]
  (A : Type*) [CommRing A] [Linear A D] (p : A) (B : D × D ⥤ D)
  (β : ∀ M M' N N' : D, (M ⟶ M') →ₗ[A] (N ⟶ N') →ₗ[A]
    (B.obj (M, N) ⟶ B.obj (M', N')))
  (hβ : ∀ (M M' N N' : D) (a : M ⟶ M') (b : N ⟶ N'),
    β M M' N N' a b = B.map (Prod.mkHom a b))

include hβ

attribute [local irreducible] tensorLocalizedAction

end TensorLocalization

end CategoryTheory.ScalarLocalization
