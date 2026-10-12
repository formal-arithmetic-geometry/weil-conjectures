/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Rlim
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv

/-!
# The underlying inverse system of a complex of towers

Let `A` be a Grothendieck abelian category. For any cochain complex `Y` of towers in `A`, the
inverse system `(evₙ (Q Y))ₙ` of `D(A)` attached to `Q Y` (`DerivedCategory.towerFunctor`) is
computed by applying `Q` to the levels `Yₙ` of `Y`: the evaluation functors are exact, so their
derived functors need no resolution (`DerivedCategory.towerFunctorQIso`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace DerivedCategory

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

/-- The level `n` of `Qh Y`, for a complex of towers `Y`, is `Qh` of the level `Yₙ`. -/
noncomputable def towerEvalQhIso (n : ℕᵒᵖ) :
    Qh ⋙ (towerEval A).obj n ≅
      ((evaluation ℕᵒᵖ A).obj n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh :=
  (asIso ((evaluation ℕᵒᵖ A).obj n).rightDerivedFunctorUnit).symm

lemma towerEvalQhIso_inv_naturality {n n' : ℕᵒᵖ} (f : n ⟶ n')
    (Y : HomotopyCategory (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) :
    (towerEvalQhIso A n).inv.app Y ≫ ((towerEval A).map f).app (Qh.obj Y) =
      Qh.map ((NatTrans.mapHomotopyCategory ((evaluation ℕᵒᵖ A).map f) _).app Y) ≫
        (towerEvalQhIso A n').inv.app Y := by
  dsimp [towerEvalQhIso, towerEval, Functor.rightDerivedFunctorNatTrans]
  exact Functor.rightDerivedNatTrans_app _ _ _ _ _ _ Y

/-- For a complex of towers `Y`, the inverse system `(evₙ (Q Y))ₙ` of `D(A)` is the image
under `Q` of the inverse system of complexes `(Yₙ)ₙ`, naturally in `Y`. -/
noncomputable def towerFunctorQIso :
    Q ⋙ towerFunctor A ≅
      (HomologicalComplex.functorEquivalence A (ComplexShape.up ℤ) ℕᵒᵖ).functor ⋙
        (Functor.whiskeringRight _ _ _).obj Q :=
  NatIso.ofComponents (fun Y ↦ NatIso.ofComponents (fun n ↦
      ((towerEval A).obj n).mapIso ((quotientCompQhIso _).app Y).symm ≪≫
        (towerEvalQhIso A n).app ((HomotopyCategory.quotient _ _).obj Y) ≪≫
          (quotientCompQhIso A).app _) (fun {n n'} f ↦ by
      have h₁ := ((towerEval A).map f).naturality ((quotientCompQhIso (ℕᵒᵖ ⥤ A)).inv.app Y)
      have h₂ := towerEvalQhIso_inv_naturality A f ((HomotopyCategory.quotient _ _).obj Y)
      have h₂' : ((towerEval A).map f).app (Qh.obj ((HomotopyCategory.quotient _ _).obj Y)) ≫
          (towerEvalQhIso A n').hom.app _ = (towerEvalQhIso A n).hom.app _ ≫
            Qh.map ((NatTrans.mapHomotopyCategory ((evaluation ℕᵒᵖ A).map f) _).app
              ((HomotopyCategory.quotient _ _).obj Y)) := by
        rw [← cancel_epi ((towerEvalQhIso A n).inv.app _), reassoc_of% h₂]
        simp
      have h₃ := (quotientCompQhIso A).hom.naturality
        ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map f) _).app Y)
      dsimp at h₁ h₃ ⊢
      rw [← reassoc_of% h₁, reassoc_of% h₂']
      rw [cancel_epi, cancel_epi]
      exact h₃.symm))
    (fun {Y Y'} (g : Y ⟶ Y') ↦ by
      ext n
      have h₁ := (quotientCompQhIso (ℕᵒᵖ ⥤ A)).inv.naturality g
      have h₂ := (towerEvalQhIso A n).hom.naturality ((HomotopyCategory.quotient _ _).map g)
      have h₃ := (quotientCompQhIso A).hom.naturality
        ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex _).map g)
      dsimp at h₁ h₂ h₃ ⊢
      rw [← Functor.map_comp_assoc, ← h₁, Functor.map_comp_assoc, reassoc_of% h₂]
      rw [cancel_epi, cancel_epi]
      exact h₃)

end DerivedCategory
