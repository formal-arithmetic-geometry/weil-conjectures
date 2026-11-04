/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
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

omit [MonoidalPreadditive C] in
/-- On the quotient map `M ⊗ N ⟶ M ⊗_R N`, the identification `- ⊗_R N ≅ - ⊗ N` is the quotient
map of the monoidal tensor product. -/
lemma tensorπ_relativeTensorRightIso_hom_app_hom (M N : Mod C R) :
    Mod.tensorπ M N ≫ ((relativeTensorRightIso N).hom.app M).hom = Mod.tensorObjπ M N := by
  have h := congrArg Mod.Hom.hom
    (show colimit.ι ((Mod.tensorLeftDiagram R N).flip.obj M) WalkingParallelPair.one ≫
        (relativeTensorRightIso N).hom.app M = relativeTensorπ M N by
      simp [relativeTensorRightIso, HasColimit.isoOfNatIso_ι_hom_assoc, relativeTensorCofork])
  exact h

omit [MonoidalPreadditive C] in
/-- The identification `- ⊗_R N ≅ - ⊗ N` is natural in `N`. -/
lemma tensorLeftMap_comp_relativeTensorRightIso_hom {M N : Mod C R} (f : M ⟶ N) :
    Mod.tensorLeftMap f ≫ (relativeTensorRightIso N).hom =
      (relativeTensorRightIso M).hom ≫ (tensoringRight _).map f := by
  apply NatTrans.ext
  funext P
  apply Mod.tensorLeft_obj_hom_ext
  simp only [NatTrans.comp_app, Mod.comp_hom']
  rw [Mod.tensorπ_tensorLeftMap_assoc]
  change P.X ◁ f.hom ≫ Mod.tensorπ P N ≫ ((relativeTensorRightIso N).hom.app P).hom = _
  rw [tensorπ_relativeTensorRightIso_hom_app_hom]
  change _ = Mod.tensorπ P M ≫ ((relativeTensorRightIso M).hom.app P).hom ≫ (P ◁ f).hom
  rw [← Category.assoc, tensorπ_relativeTensorRightIso_hom_app_hom]
  exact (Mod.tensorObjπ_whiskerLeft f).symm

/-- The tensor product `M ⊗ -` of modules is `- ⊗_R M`, through the symmetry. -/
noncomputable def tensorLeftIsoModTensorLeft (M : Mod C R) :
    MonoidalCategory.tensorLeft M ≅ Mod.tensorLeft M :=
  BraidedCategory.tensorLeftIsoTensorRight M ≪≫ (relativeTensorRightIso M).symm

omit [MonoidalPreadditive C] in
lemma tensorLeftIsoModTensorLeft_hom_comp_tensorLeftMap {M N : Mod C R} (f : M ⟶ N) :
    (tensorLeftIsoModTensorLeft M).hom ≫ Mod.tensorLeftMap f =
      (tensoringLeft _).map f ≫ (tensorLeftIsoModTensorLeft N).hom := by
  apply (cancel_mono (relativeTensorRightIso N).hom).1
  rw [Category.assoc, tensorLeftMap_comp_relativeTensorRightIso_hom]
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
