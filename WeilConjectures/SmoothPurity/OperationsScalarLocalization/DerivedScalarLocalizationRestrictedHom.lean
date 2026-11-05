/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.Ring

/-! # Scalar localization of a permitted contravariant bilinear functor

Extracted proved scalar-localization calculus used by the derived-operation construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v r s u₁ v₁ u₂ v₂
open Opposite TensorProduct CategoryTheory
namespace WeilConjectures.OperationsScalarLocalization

section HomLocalization
set_option backward.defeqAttrib.useBackward false
variable {D : Type*} [Category* D] [Preadditive D]
  (A : Type*) [CommRing A] [Linear A D] (p : A)
  (q : ObjectProperty (Dᵒᵖ × D)) (B : q.FullSubcategory ⥤ D)

variable (q' : ObjectProperty ((ScalarLocalization A D p)ᵒᵖ × ScalarLocalization A D p))
  (hq' : ∀ X, q' X → q (op X.1.unop.obj, X.2.obj))

variable (β : ∀ P Q : q.FullSubcategory,
    (Q.obj.1.unop ⟶ P.obj.1.unop) →ₗ[A] (P.obj.2 ⟶ Q.obj.2) →ₗ[A]
      (B.obj P ⟶ B.obj Q))
  (hβ : ∀ (P Q : q.FullSubcategory)
    (a : Q.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ Q.obj.2),
    β P Q a b = B.map (ObjectProperty.homMk (Prod.mkHom a.op b)))

include hβ

attribute [local irreducible] homLocalizedAction

end HomLocalization

end WeilConjectures.OperationsScalarLocalization
