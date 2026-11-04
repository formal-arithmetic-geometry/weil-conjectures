/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose

/-!
# The two internal homs of modules agree

Let `R` be a commutative monoid in a closed symmetric monoidal Grothendieck abelian category `C`.
The category `Mod C R` has two internal homs: the internal hom `Hom_R(M, -) = Mod.ihom M`, right
adjoint to `- ⊗_R M` (`Mod.tensorLeft M`, a coequalizer), and the internal hom `ihom M` of the
monoidal closed structure `Mod.monoidalClosed`, right adjoint to `M ⊗ -` for the monoidal
structure of `Mod C R`. This file identifies them, naturally in both variables
(`CategoryTheory.Mod.ihomIsoIhom`, `CategoryTheory.Mod.ihomMap_comp_ihomIsoIhom_hom`): the two
tensor products are the same coequalizer, up to the symmetry.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- The quotient map defining the relative tensor product is linear in its first factor. -/
noncomputable def relativeTensorπ (M N : Mod C R) :
    (Mod.tensorRight R N.X).obj M ⟶ M ⊗ N :=
  homMk (M := (Mod.tensorRight R N.X).obj M) (N := M ⊗ N) (tensorObjπ M N) (by
    change ((α_ R M.X N.X).inv ≫ γ[R,M.X] ▷ N.X) ≫ tensorObjπ M N =
      R ◁ tensorObjπ M N ≫ γ[R,(M ⊗ N).X]
    simpa only [Category.assoc] using (whiskerLeft_tensorπ_smul M N).symm)

/-- The relative tensor product is a cofork of the two action maps on module objects. -/
noncomputable def relativeTensorCofork (M N : Mod C R) :
    Cofork ((tensorRightMap R γ[R,N.X]).app M) ((tensorRightRightAct R N.X).app M) :=
  Cofork.ofπ (relativeTensorπ M N) (by
    apply Mod.hom_ext
    change M.X ◁ γ[R,N.X] ≫ tensorObjπ M N =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ tensorObjπ M N
    rw [Category.assoc, tensorObjπ_condition]
    simp only [Category.assoc, Iso.inv_hom_id_assoc])

/-- The tensor cofork is a coequalizer, as can be checked after forgetting the module action. -/
noncomputable def isColimitRelativeTensorCofork (M N : Mod C R) :
    IsColimit (relativeTensorCofork M N) := by
  apply isColimitOfIsColimitCoforkMap (forget R)
  change IsColimit (Cofork.ofπ (tensorObjπ M N) _ :
    Cofork (M.X ◁ γ[R,N.X]) ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X))
  refine Cofork.IsColimit.mk _
    (fun s ↦ coequalizer.desc (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) s.π ?_) ?_ ?_
  · have h := s.condition
    change M.X ◁ γ[R,N.X] ≫ s.π =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ s.π at h
    rw [← cancel_epi (α_ M.X R N.X).inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  · intro s
    exact coequalizer.π_desc _ _
  · intro s m hm
    apply coequalizer.hom_ext (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X])
    exact hm.trans (coequalizer.π_desc _ _).symm

/-- The two relative tensor products agree: `M ⊗_R N ≅ M ⊗ N`. -/
noncomputable def tensorLeftObjIso (M N : Mod C R) : (Mod.tensorLeft N).obj M ≅ M ⊗ N :=
  HasColimit.isoOfNatIso
    (diagramIsoParallelPair ((Mod.tensorLeftDiagram R N).flip.obj M)) ≪≫
      (colimit.isColimit _).coconePointUniqueUpToIso (isColimitRelativeTensorCofork M N)

omit [MonoidalPreadditive C] in
lemma tensorπ_tensorLeftObjIso_hom (M N : Mod C R) :
    Mod.tensorπ M N ≫ (tensorLeftObjIso M N).hom.hom = Mod.tensorObjπ M N := by
  have h := congrArg Mod.Hom.hom
    (show colimit.ι ((Mod.tensorLeftDiagram R N).flip.obj M) WalkingParallelPair.one ≫
        (tensorLeftObjIso M N).hom = relativeTensorπ M N by
      simp [tensorLeftObjIso, HasColimit.isoOfNatIso_ι_hom_assoc, relativeTensorCofork])
  exact h

/-- The tensor product `- ⊗_R N` of modules is `- ⊗ N`. -/
noncomputable def tensorLeftIsoTensorRight (N : Mod C R) :
    Mod.tensorLeft N ≅ MonoidalCategory.tensorRight N :=
  NatIso.ofComponents (fun M ↦ tensorLeftObjIso M N) (by
    intro M M' f
    apply Mod.tensorLeft_obj_hom_ext
    simp only [Mod.comp_hom', Mod.tensorπ_map_assoc]
    rw [tensorπ_tensorLeftObjIso_hom, ← Category.assoc, tensorπ_tensorLeftObjIso_hom]
    exact (Mod.tensorObjπ_whiskerRight f).symm)

omit [MonoidalPreadditive C] in
lemma tensorLeftMap_comp_tensorLeftIsoTensorRight_hom {M N : Mod C R} (f : M ⟶ N) :
    Mod.tensorLeftMap f ≫ (tensorLeftIsoTensorRight N).hom =
      (tensorLeftIsoTensorRight M).hom ≫ (tensoringRight _).map f := by
  apply NatTrans.ext
  funext P
  apply Mod.tensorLeft_obj_hom_ext
  simp only [NatTrans.comp_app, Mod.comp_hom']
  rw [Mod.tensorπ_tensorLeftMap_assoc]
  change P.X ◁ f.hom ≫ Mod.tensorπ P N ≫ (tensorLeftObjIso P N).hom.hom = _
  rw [tensorπ_tensorLeftObjIso_hom]
  change _ = Mod.tensorπ P M ≫ (tensorLeftObjIso P M).hom.hom ≫ (P ◁ f).hom
  rw [← Category.assoc, tensorπ_tensorLeftObjIso_hom]
  exact (Mod.tensorObjπ_whiskerLeft f).symm

/-- The tensor product `M ⊗ -` of modules is `- ⊗_R M`, through the symmetry. -/
noncomputable def tensorLeftIsoModTensorLeft (M : Mod C R) :
    MonoidalCategory.tensorLeft M ≅ Mod.tensorLeft M :=
  BraidedCategory.tensorLeftIsoTensorRight M ≪≫ (tensorLeftIsoTensorRight M).symm

omit [MonoidalPreadditive C] in
lemma tensorLeftIsoModTensorLeft_hom_comp_tensorLeftMap {M N : Mod C R} (f : M ⟶ N) :
    (tensorLeftIsoModTensorLeft M).hom ≫ Mod.tensorLeftMap f =
      (tensoringLeft _).map f ≫ (tensorLeftIsoModTensorLeft N).hom := by
  apply (cancel_mono (tensorLeftIsoTensorRight N).hom).1
  rw [Category.assoc, tensorLeftMap_comp_tensorLeftIsoTensorRight_hom]
  simp only [tensorLeftIsoModTensorLeft, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply NatTrans.ext
  funext P
  exact (BraidedCategory.braiding_naturality_left f P).symm

/-- **The two internal homs of modules agree**: `Hom_R(M, -) ≅ [M, -]`. -/
noncomputable def ihomIsoIhom (M : Mod C R) : Mod.ihom M ≅ CategoryTheory.ihom M :=
  conjugateIsoEquiv (Mod.ihomAdjunction M) (CategoryTheory.ihom.adjunction M)
    (tensorLeftIsoModTensorLeft M)

/-- The identification `Hom_R(M, -) ≅ [M, -]` is natural in `M`. -/
@[reassoc]
lemma ihomMap_comp_ihomIsoIhom_hom {M N : Mod C R} (f : M ⟶ N) :
    Mod.ihomMap f ≫ (ihomIsoIhom M).hom = (ihomIsoIhom N).hom ≫ MonoidalClosed.pre f := by
  change conjugateEquiv (Mod.ihomAdjunction N) (Mod.ihomAdjunction M)
      (Mod.tensorLeftMap f) ≫
      conjugateEquiv (Mod.ihomAdjunction M) (CategoryTheory.ihom.adjunction M)
        (tensorLeftIsoModTensorLeft M).hom =
    conjugateEquiv (Mod.ihomAdjunction N) (CategoryTheory.ihom.adjunction N)
      (tensorLeftIsoModTensorLeft N).hom ≫
      conjugateEquiv (CategoryTheory.ihom.adjunction N) (CategoryTheory.ihom.adjunction M)
        ((tensoringLeft _).map f)
  rw [conjugateEquiv_comp, conjugateEquiv_comp, tensorLeftIsoModTensorLeft_hom_comp_tensorLeftMap]

end CategoryTheory.Mod
