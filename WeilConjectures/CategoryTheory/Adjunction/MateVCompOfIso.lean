/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates of squares stacked along composites of the non-adjoint sides

Consider adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂`, `L₃ ⊣ R₃` and squares
```
      L₁            L₂            L₁
   A ---→ B      C ---→ D      A ---→ B
G₁ ↓  α₁  ↓ H₁  G₂ ↓ α₂  ↓ H₂   G ↓  α   ↓ H
   C ---→ D      E ---→ F      E ---→ F
      L₂            L₃            L₃
```
together with isomorphisms `κ : G ≅ G₁ ⋙ G₂` and `κ' : H ≅ H₁ ⋙ H₂` under which `α` is the
vertical composite of `α₁` and `α₂`. Then the mate of `α` is the vertical composite of the mates
of `α₁` and `α₂` under `κ` and `κ'` (`CategoryTheory.mateEquiv_app_eq_comp_of_vComp_iso`), and in
particular it is invertible at an object as soon as the mates of `α₁` and `α₂` are invertible at
the appropriate objects (`CategoryTheory.isIso_mateEquiv_app_of_vComp_iso`).

The intended case: `L = Lf^*` derived pullbacks with coefficients `Λ`, `Λ'`, `Λ''`, and
`G`, `H` derived extensions of scalars along a composite coefficient change `Λ ⟶ Λ' ⟶ Λ''`.
-/

@[expose] public section

namespace CategoryTheory

variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* E] [Category* F]
  {G₁ : A ⥤ C} {G₂ : C ⥤ E} {G : A ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F} {H : B ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : E ⥤ F} {R₃ : F ⥤ E}

/-- The mate of a square whose non-adjoint sides are composites `G ≅ G₁ ⋙ G₂` and
`H ≅ H₁ ⋙ H₂`, and which is the vertical composite of two squares under these isomorphisms, is
the vertical composite of the two mates. -/
lemma mateEquiv_app_eq_comp_of_vComp_iso (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (κ : G ≅ G₁ ⋙ G₂) (κ' : H ≅ H₁ ⋙ H₂) (α₁ : TwoSquare G₁ L₁ L₂ H₁)
    (α₂ : TwoSquare G₂ L₂ L₃ H₂) (α : TwoSquare G L₁ L₃ H)
    (h : ∀ M, α.natTrans.app M = L₃.map (κ.hom.app M) ≫ α₂.natTrans.app (G₁.obj M) ≫
      H₂.map (α₁.natTrans.app M) ≫
      κ'.inv.app (L₁.obj M)) (K : B) :
    (mateEquiv adj₁ adj₃ α).natTrans.app K = κ.hom.app (R₁.obj K) ≫
      G₂.map ((mateEquiv adj₁ adj₂ α₁).natTrans.app K) ≫
      (mateEquiv adj₂ adj₃ α₂).natTrans.app (H₁.obj K) ≫
      R₃.map (κ'.inv.app K) := by
  have e := NatTrans.congr_app (mateEquiv_vcomp adj₁ adj₂ adj₃ α₁ α₂) K
  simp [TwoSquare.vComp, TwoSquare.hComp, mateEquiv_apply] at e
  have hn := κ'.inv.naturality (adj₁.counit.app K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  simp only [Functor.comp_obj, mateEquiv_apply, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp, Functor.map_comp,
    Category.assoc, h]
  rw [← R₃.map_comp (κ'.inv.app _), ← hn, R₃.map_comp]
  simp only [← Category.assoc]
  congr 1
  simpa using e

end CategoryTheory
