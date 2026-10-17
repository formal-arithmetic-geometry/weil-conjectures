/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom

/-!

# Module objects over a commutative algebra object form a closed monoidal category

Let `C` be a symmetric monoidal closed category with equalizers and coequalizers, and `R : C` a
commutative algebra object. The category `Mod C R` carries two descriptions of the relative
tensor product `P ⊗_R M`:

* the monoidal structure of `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`, induced from
  the tensor product of bimodules, presenting `P ⊗_R M` as a coequalizer in `C`;
* the functor `Mod.tensorLeft M : P ↦ P ⊗_A M` of
  `WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor`,
  defined as a coequalizer in `Mod C R`, which has the concrete right adjoint
  `Mod.ihom' R M` (the equalizer of `[M, N] ⇉ [R ⊗ M, N]`, see `Mod.ihom'Adjunction`).

We identify the two (`Mod.tensorLeftIsoTensorRight`); combined with the braiding of `Mod C R`,
this makes `M ⊗_R -` left adjoint to `Mod.ihom' R M`, so that `Mod C R` is monoidal closed
(`Mod.monoidalClosedOfSymmetric`).

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

section Comparison

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
  [BraidedCategory C] {R : C} [MonObj R] [IsCommMonObj R]

/-- The projection `P ⊗ M ⟶ P ⊗_R M`, as a morphism of `R`-modules (`R` acting on `P`). -/
noncomputable def tensorObjπHom (P M : Mod C R) : (tensorRight R M.X).obj P ⟶ P ⊗ M :=
  homMk (M := (tensorRight R M.X).obj P) (tensorObjπ P M) (by
    change ((α_ R P.X M.X).inv ≫ act P.X ▷ M.X) ≫ tensorObjπ P M = _
    rw [whiskerLeft_tensorπ_smul, Category.assoc])

@[simp]
lemma tensorObjπHom_hom (P M : Mod C R) : (tensorObjπHom P M).hom = tensorObjπ P M := rfl

lemma tensorRightRightAct_comp_tensorObjπHom (P M : Mod C R) :
    (tensorRightRightAct R M.X).app P ≫ tensorObjπHom P M =
      (tensorRightMap R (act M.X)).app P ≫ tensorObjπHom P M := by
  refine Mod.hom_ext _ _ ?_
  change ((α_ P.X R M.X).inv ≫ rightAct P ▷ M.X) ≫ tensorObjπ P M =
    P.X ◁ act M.X ≫ tensorObjπ P M
  rw [Category.assoc, rightAct, tensorObjπ_condition, ← Category.assoc, Iso.inv_hom_id_assoc]

/-- The cocone on the parallel pair defining `P ⊗_A M` (`Mod.tensorLeft`) with vertex the
relative tensor product `P ⊗ M` of the monoidal structure of `Mod C R`. -/
noncomputable def tensorObjCocone (P M : Mod C R) :
    Cocone ((tensorLeftDiagram R M).flip.obj P) where
  pt := P ⊗ M
  ι :=
    { app j := match j with
        | .zero => (tensorRightMap R (act M.X)).app P ≫ tensorObjπHom P M
        | .one => tensorObjπHom P M
      naturality := by
        rintro _ _ (_ | _ | _)
        · exact (Category.comp_id _).symm
        · exact (tensorRightRightAct_comp_tensorObjπHom P M).trans (Category.comp_id _).symm
        · simp }

/-- The comparison map `P ⊗_A M ⟶ P ⊗ M` from `Mod.tensorLeft` to the monoidal structure. -/
noncomputable def tensorLeftToTensorObj (P M : Mod C R) : (tensorLeft M).obj P ⟶ P ⊗ M :=
  colimit.desc _ (tensorObjCocone P M)

@[reassoc (attr := simp)]
lemma ι_tensorLeftToTensorObj (P M : Mod C R) :
    colimit.ι ((tensorLeftDiagram R M).flip.obj P) .one ≫ tensorLeftToTensorObj P M =
      tensorObjπHom P M :=
  colimit.ι_desc _ _

omit [HasCoequalizers C] [IsCommMonObj R]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)] in
lemma rightAct_whiskerRight_comp_of_eq (P M : Mod C R) {Y : C} (x : P.X ⊗ M.X ⟶ Y)
    (h : P.X ◁ act M.X ≫ x = (α_ P.X R M.X).inv ≫ rightAct P ▷ M.X ≫ x) :
    ((β_ P.X R).hom ≫ act P.X) ▷ M.X ≫ x = ((α_ P.X R M.X).hom ≫ P.X ◁ act M.X) ≫ x := by
  rw [Category.assoc, h, Iso.hom_inv_id_assoc]

/-- The inverse of `tensorLeftToTensorObj` on the underlying objects. -/
noncomputable def tensorObjToTensorLeftX (P M : Mod C R) : (P ⊗ M).X ⟶ ((tensorLeft M).obj P).X :=
  Cofork.IsColimit.desc (isColimitTensorπ P M)
    (colimit.ι ((tensorLeftDiagram R M).flip.obj P) .one).hom
    (rightAct_whiskerRight_comp_of_eq P M _ (by
      have h₁ := colimit.w ((tensorLeftDiagram R M).flip.obj P) WalkingParallelPairHom.left
      have h₂ := colimit.w ((tensorLeftDiagram R M).flip.obj P) WalkingParallelPairHom.right
      have h := congrArg Mod.Hom.hom (h₁.trans h₂.symm)
      simp only [Mod.comp_hom'] at h
      exact h.trans (Category.assoc _ _ _)))

@[reassoc (attr := simp)]
lemma tensorObjπ_tensorObjToTensorLeftX (P M : Mod C R) :
    tensorObjπ P M ≫ tensorObjToTensorLeftX P M =
      (colimit.ι ((tensorLeftDiagram R M).flip.obj P) .one).hom :=
  Cofork.IsColimit.π_desc' (isColimitTensorπ P M) _ _

instance (P M : Mod C R) : IsIso (tensorLeftToTensorObj P M) := by
  have : IsIso (tensorLeftToTensorObj P M).hom := by
    refine ⟨tensorObjToTensorLeftX P M, ?_, ?_⟩
    · refine (isColimitOfPreserves (forget R)
        (colimit.isColimit ((tensorLeftDiagram R M).flip.obj P))).hom_ext fun j ↦ ?_
      have h₁ : (colimit.ι ((tensorLeftDiagram R M).flip.obj P) .one).hom ≫
          (tensorLeftToTensorObj P M).hom ≫ tensorObjToTensorLeftX P M =
            (colimit.ι ((tensorLeftDiagram R M).flip.obj P) .one).hom := by
        rw [← Category.assoc, ← Mod.comp_hom', ι_tensorLeftToTensorObj, tensorObjπHom_hom,
          tensorObjπ_tensorObjToTensorLeftX]
      cases j
      · change (colimit.ι ((tensorLeftDiagram R M).flip.obj P) .zero).hom ≫ _ =
          (colimit.ι ((tensorLeftDiagram R M).flip.obj P) .zero).hom ≫ 𝟙 _
        rw [← colimit.w ((tensorLeftDiagram R M).flip.obj P) WalkingParallelPairHom.left,
          Mod.comp_hom', Category.assoc, h₁, Category.assoc, Category.comp_id]
      · exact h₁.trans (Category.comp_id _).symm
    · rw [← cancel_epi (tensorObjπ P M), tensorObjπ_tensorObjToTensorLeftX_assoc,
        ← Mod.comp_hom', ι_tensorLeftToTensorObj, tensorObjπHom_hom, Category.comp_id]
  have : IsIso ((forget R).map (tensorLeftToTensorObj P M)) := this
  exact isIso_of_reflects_iso _ (forget R)

variable (R) in
/-- **The two relative tensor products agree**: `Mod.tensorLeft M` is the functor
`P ↦ P ⊗ M` of the monoidal structure of `Mod C R`. -/
noncomputable def tensorLeftIsoTensorRight (M : Mod C R) :
    tensorLeft M ≅ MonoidalCategory.tensorRight M :=
  NatIso.ofComponents (fun P ↦ asIso (tensorLeftToTensorObj P M)) fun {P Q} f ↦ by
    refine colimit.hom_ext fun j ↦ ?_
    change colimit.ι _ j ≫ colim.map ((tensorLeftDiagram R M).flip.map f) ≫ _ = _
    rw [colimit.ι_map_assoc]
    simp only [asIso_hom, tensorLeftToTensorObj, colimit.ι_desc, colimit.ι_desc_assoc]
    have key : (tensorRight R M.X).map f ≫ tensorObjπHom Q M = tensorObjπHom P M ≫ f ▷ M :=
      Mod.hom_ext _ _ (tensorObjπ_whiskerRight f).symm
    cases j
    · change ((tensorRight R (R ⊗ M.X)).map f) ≫ (tensorRightMap R (act M.X)).app Q ≫
          tensorObjπHom Q M = ((tensorRightMap R (act M.X)).app P ≫ tensorObjπHom P M) ≫ f ▷ M
      rw [reassoc_of% ((tensorRightMap R (act M.X)).naturality f), key, Category.assoc]
    · exact key

end Comparison

section Closed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- **The tensor–hom adjunction for the relative tensor product**: `M ⊗_R -` is left adjoint to
the internal hom `Hom_R(M, -)` of `Mod.ihom'`. -/
noncomputable def tensorLeftIhom'Adjunction (M : Mod C R) :
    MonoidalCategory.tensorLeft M ⊣ ihom' R M :=
  (ihom'Adjunction R M).ofNatIsoLeft
    (tensorLeftIsoTensorRight R M ≪≫ (BraidedCategory.tensorLeftIsoTensorRight M).symm)

/-- The category of module objects over a commutative algebra object in a symmetric monoidal
closed category with equalizers and coequalizers is monoidal closed, with internal hom
`Mod.ihom'`. -/
@[instance_reducible]
noncomputable def monoidalClosedOfSymmetric : MonoidalClosed (Mod C R) where
  closed M := { rightAdj := ihom' R M, adj := tensorLeftIhom'Adjunction M }

end Closed

end CategoryTheory.Mod
