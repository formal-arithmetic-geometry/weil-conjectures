/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Opposites

/-!
# Anti-equivalences from a double-dual isomorphism

A contravariant functor `D : Cᵒᵖ ⥤ C` with a natural isomorphism `δ : 𝟭 C ≅ D.rightOp ⋙ D`
(the shape of a duality with its double-dual isomorphism `K ≅ D (D K)`) is an anti-equivalence:
`CategoryTheory.Functor.dualEquivalence D δ : Cᵒᵖ ≌ C`, with functor `D` and quasi-inverse
`D.rightOp`.
-/

@[expose] public section

open Opposite

namespace CategoryTheory

/-- A contravariant functor `D : Cᵒᵖ ⥤ C` with a natural isomorphism `δ : 𝟭 C ≅ D.rightOp ⋙ D`
is an anti-equivalence: `D.rightOp : C ⥤ Cᵒᵖ` is an equivalence, with quasi-inverse `D`. -/
@[simps! functor inverse]
noncomputable def Functor.dualEquivalence {C : Type*} [Category* C] (D : Cᵒᵖ ⥤ C)
    (δ : 𝟭 C ≅ D.rightOp ⋙ D) : Cᵒᵖ ≌ C :=
  Equivalence.mk D D.rightOp
    (NatIso.ofComponents (fun K ↦ (δ.app K.unop).op.symm) fun f ↦
      Quiver.Hom.unop_inj (by simpa using (δ.inv.naturality f.unop).symm))
    (NatIso.ofComponents (fun K ↦ (δ.app K).symm) fun f ↦ by simpa using δ.inv.naturality f)

end CategoryTheory
