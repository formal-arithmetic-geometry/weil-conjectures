/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic

/-! # Assembly of a specified tensor comparison arrow -/

@[expose] public section
set_option autoImplicit false

universe u v w z
open CategoryTheory

namespace WeilConjectures

/-- Compose a coefficient tensor comparison, two specified cancellation arrows,
and the tensor-completion comparison. Checking this composition for abstract
categories avoids repeated expansion of the concrete coefficient category.
Source: the tensor comparison composite in fix-prop-projection-formula,
projection-formula proof step 13.
(blueprint: def-sf-projection-tensor-arrow-assembly). -/
def projectionTensorArrowAssembly
    {A : Type u} {B : Type v} [Category.{w} A] [Category.{z} B]
    (T : A × A ⥤ A) (G : A ⥤ B) (R S : B × B ⥤ B)
    (α : T ⋙ G ≅ (G.prod G) ⋙ R) (χ : R ≅ S)
    (K L : A) (M N : B) (a : G.obj K ⟶ M) (b : G.obj L ⟶ N) :
    G.obj (T.obj (K, L)) ⟶ S.obj (M, N) :=
  α.hom.app (K, L) ≫ R.map (Prod.mkHom a b) ≫ χ.hom.app (M, N)

end WeilConjectures
