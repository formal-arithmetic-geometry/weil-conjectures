/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Transport of adjunctions with a parameter along an equivalence

If an equivalence `E : C ≌ D` intertwines the left adjoints of adjunctions with a parameter
`T ⊣₂ H` on `C` and `T' ⊣₂ H'` on `D`, it intertwines their right adjoints, naturally in both
variables (`CategoryTheory.ParametrizedAdjunction.transportIso`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite CategoryTheory.Functor

namespace ParametrizedAdjunction

section Equivalence

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C} {T' : D ⥤ D ⥤ D} {H' : Dᵒᵖ ⥤ D ⥤ D}

/-- Transport of the right adjoint along an equivalence: if an equivalence `E : C ≌ D`
intertwines the left adjoints of adjunctions with a parameter `T ⊣₂ H` on `C` and `T' ⊣₂ H'`
on `D`, `E (T P X) ≅ T' (E P) (E X)` naturally in `P` and `X`, then it intertwines the right
adjoints: `E (H P Q) ≅ H' (E P) (E Q)`, naturally in `P` and `Q`. -/
noncomputable def transportIso (adj : T ⊣₂ H) (adj' : T' ⊣₂ H') (E : C ≌ D)
    (τ : T ⋙ (whiskeringRight C C D).obj E.functor ≅
      E.functor ⋙ T' ⋙ (whiskeringLeft C D D).obj E.functor) :
    H ⋙ (whiskeringRight C C D).obj E.functor ≅
      E.functor.op ⋙ H' ⋙ (whiskeringLeft C D D).obj E.functor :=
  (adj.comp E.symm.toAdjunction (Adjunction.id (C := C))).conjugateIso
    ((adj'.precomp E.functor).comp (Adjunction.id (C := D)) E.symm.toAdjunction)
    (NatIso.ofComponents (fun P ↦ NatIso.ofComponents (fun Y ↦
      E.inverse.mapIso ((T'.obj (E.functor.obj P)).mapIso (E.counitIso.app Y).symm ≪≫
        ((τ.app P).app (E.inverse.obj Y)).symm) ≪≫ (E.unitIso.app _).symm) (by
          intro Y Y' f
          have h₁ := (τ.inv.app P).naturality (E.inverse.map f)
          have h₂ := E.unitIso.inv.naturality ((T.obj P).map (E.inverse.map f))
          have h₃ := E.counitIso.inv.naturality f
          dsimp at h₁ h₂ h₃ ⊢
          rw [Category.assoc, ← h₂]
          simp only [← Functor.map_comp_assoc, Category.assoc]
          congr 2
          rw [← h₁, ← Functor.map_comp_assoc, ← h₃, Functor.map_comp_assoc])) (by
      intro P P' g
      ext Y
      have h₁ := NatTrans.congr_app (τ.inv.naturality g) (E.inverse.obj Y)
      have h₂ := E.unitIso.inv.naturality ((T.map g).app (E.inverse.obj Y))
      dsimp at h₁ h₂ ⊢
      rw [Category.assoc, ← h₂]
      simp only [← Functor.map_comp_assoc, Category.assoc]
      congr 2
      rw [← h₁, ← NatTrans.naturality_assoc]))

end Equivalence

end ParametrizedAdjunction

end CategoryTheory
