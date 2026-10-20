/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y5
-/
module

public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.DerivedBraided
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # The native localization tensor at independent ringed-site universes

Source: Stacks Project, Tags 06YS, 06YT and 0FPT.
(blueprint: lem-sf-ringed-derived-native-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open WeilConjectures Opposite

namespace CategoryTheory.RingedDerivedNative

/-- Symmetry descends through the native derived-monoidal localization.
Source: Stacks Project, Tag 0FPT; uniqueness of derived natural transformations. -/
@[instance_reducible]
def localizedSymmetric {A B : Type*} [Category A] [Category B]
    [MonoidalCategory A] [SymmetricCategory A] (L : A ⥤ B) (W : MorphismProperty A)
    [L.IsLocalization W] [W.ContainsIdentities] [L.HasDerivedMonoidalCategory W]
    [W.RespectsIso] [W.localizerMorphismKFlat.IsLeftDerivabilityStructure]
    [W.HasTwoOutOfThreeProperty] : SymmetricCategory (DerivedMonoidal L W) := by
  let := DerivedMonoidal.braidedCategory' L W
  refine { toBraidedCategory := inferInstance, symmetry := ?_ }
  intro X Y
  have he : DerivedMonoidal.braidingInvCounit L W =
      DerivedMonoidal.braidingCounit L W := by
    apply NatTrans.ext
    funext A
    apply NatTrans.ext
    funext B
    change _ ≫ L.map (β_ A B).inv = _ ≫ L.map (β_ B A).hom
    rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
  have ht : DerivedMonoidal.braidingInvNatTrans L W =
      DerivedMonoidal.braidingNatTrans L W := by
    unfold DerivedMonoidal.braidingInvNatTrans DerivedMonoidal.braidingNatTrans
    rw [he]
  change (DerivedMonoidal.braiding' L W X Y).hom ≫
    ((DerivedMonoidal.braidingNatTrans L W).app X).app Y = _
  rw [← ht]
  exact (DerivedMonoidal.braiding' L W X Y).hom_inv_id


/-- The Koszul braiding of complexes over a symmetric category is involutive. -/
theorem complex_symmetry {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
    [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (P L : CochainComplex A ℤ) :
    (β_ P L).hom ≫ (β_ L P).hom = 𝟙 _ := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ← Category.assoc]
  change (HomologicalComplex.ιTensorObj P L p q n h ≫
    (CochainComplex.Monoidal.braiding P L).hom.f n) ≫
      (CochainComplex.Monoidal.braiding L P).hom.f n = _
  rw [CochainComplex.Monoidal.ι_braiding_hom]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [CochainComplex.Monoidal.ι_braiding_hom]
  simp only [Preadditive.comp_zsmul, ← Category.assoc, SymmetricCategory.symmetry,
    Category.id_comp, smul_smul, mul_comm q p]
  simp only [← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  exact (Category.comp_id _).symm



section InverseTensorator
variable {A B : Type*} [Category* A] [Category* B]
  [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B) [F.LaxMonoidal]

/-- Inverse tensorators are natural wherever both components are invertible. -/
theorem inverse_naturality {X Y X' Y' : A} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsIso (Functor.LaxMonoidal.μ F X Y)]
    [IsIso (Functor.LaxMonoidal.μ F X' Y')] :
    F.map (f ⊗ₘ g) ≫ inv (Functor.LaxMonoidal.μ F X' Y') =
      inv (Functor.LaxMonoidal.μ F X Y) ≫ (F.map f ⊗ₘ F.map g) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F X Y)).1
  rw [← Category.assoc, ← Functor.LaxMonoidal.μ_natural, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id, ← Category.assoc,
    IsIso.hom_inv_id, Category.id_comp]

/-- Invertible components of a lax tensorator preserve reassociation. -/
theorem inverse_associativity (X Y Z : A)
    [IsIso (Functor.LaxMonoidal.μ F X Y)]
    [IsIso (Functor.LaxMonoidal.μ F Y Z)]
    [IsIso (Functor.LaxMonoidal.μ F (X ⊗ Y) Z)]
    [IsIso (Functor.LaxMonoidal.μ F X (Y ⊗ Z))] :
    inv (Functor.LaxMonoidal.μ F (X ⊗ Y) Z) ≫
        inv (Functor.LaxMonoidal.μ F X Y) ▷ F.obj Z ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ inv (Functor.LaxMonoidal.μ F X (Y ⊗ Z)) ≫
        F.obj X ◁ inv (Functor.LaxMonoidal.μ F Y Z) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F X Y ▷ F.obj Z ≫
    Functor.LaxMonoidal.μ F (X ⊗ Y) Z)).1
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight,
    Category.id_comp, Functor.LaxMonoidal.associativity_assoc,
    IsIso.hom_inv_id_assoc, ← whiskerLeft_comp, IsIso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- Inverting the tensorator and the unit comparison preserves the left unitor. -/
theorem inverse_leftUnitor (X : A) [IsIso (Functor.LaxMonoidal.ε F)]
    [IsIso (Functor.LaxMonoidal.μ F (𝟙_ A) X)] :
    inv (Functor.LaxMonoidal.μ F (𝟙_ A) X) ≫
      inv (Functor.LaxMonoidal.ε F) ▷ F.obj X ≫ (λ_ (F.obj X)).hom =
        F.map (λ_ X).hom := by
  rw [Functor.LaxMonoidal.left_unitality F]
  simp only [← Category.assoc, ← comp_whiskerRight, IsIso.inv_hom_id,
    id_whiskerRight, Category.id_comp]

/-- Inverting the tensorator and the unit comparison preserves the right unitor. -/
theorem inverse_rightUnitor (X : A) [IsIso (Functor.LaxMonoidal.ε F)]
    [IsIso (Functor.LaxMonoidal.μ F X (𝟙_ A))] :
    inv (Functor.LaxMonoidal.μ F X (𝟙_ A)) ≫
      F.obj X ◁ inv (Functor.LaxMonoidal.ε F) ≫ (ρ_ (F.obj X)).hom =
        F.map (ρ_ X).hom := by
  rw [Functor.LaxMonoidal.right_unitality F]
  simp only [← Category.assoc, ← whiskerLeft_comp, IsIso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]


/-- Tensor-morphism form of the inverse associativity equation. -/
theorem inverse_associativity_tensor (X Y Z : A)
    [IsIso (Functor.LaxMonoidal.μ F X Y)]
    [IsIso (Functor.LaxMonoidal.μ F Y Z)]
    [IsIso (Functor.LaxMonoidal.μ F (X ⊗ Y) Z)]
    [IsIso (Functor.LaxMonoidal.μ F X (Y ⊗ Z))] :
    inv (Functor.LaxMonoidal.μ F (X ⊗ Y) Z) ≫
        (inv (Functor.LaxMonoidal.μ F X Y) ⊗ₘ 𝟙 (F.obj Z)) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ inv (Functor.LaxMonoidal.μ F X (Y ⊗ Z)) ≫
        (𝟙 (F.obj X) ⊗ₘ inv (Functor.LaxMonoidal.μ F Y Z)) := by
  rw [tensorHom_id, id_tensorHom]
  exact inverse_associativity F X Y Z

/-- Tensor-morphism form of the inverse left-unit equation. -/
theorem inverse_leftUnitor_tensor (X : A) [IsIso (Functor.LaxMonoidal.ε F)]
    [IsIso (Functor.LaxMonoidal.μ F (𝟙_ A) X)] :
    inv (Functor.LaxMonoidal.μ F (𝟙_ A) X) ≫
      (inv (Functor.LaxMonoidal.ε F) ⊗ₘ 𝟙 (F.obj X)) ≫
        (λ_ (F.obj X)).hom = F.map (λ_ X).hom := by
  rw [tensorHom_id]
  exact inverse_leftUnitor F X

/-- Tensor-morphism form of the inverse right-unit equation. -/
theorem inverse_rightUnitor_tensor (X : A) [IsIso (Functor.LaxMonoidal.ε F)]
    [IsIso (Functor.LaxMonoidal.μ F X (𝟙_ A))] :
    inv (Functor.LaxMonoidal.μ F X (𝟙_ A)) ≫
      (𝟙 (F.obj X) ⊗ₘ inv (Functor.LaxMonoidal.ε F)) ≫
        (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom := by
  rw [id_tensorHom]
  exact inverse_rightUnitor F X

end InverseTensorator

section BraidedTensorator
variable {A B : Type*} [Category* A] [Category* B]
  [MonoidalCategory A] [MonoidalCategory B] [BraidedCategory A] [BraidedCategory B]
  (F : A ⥤ B) [F.LaxBraided]

/-- Inverting an invertible lax tensorator gives the usual braiding square. -/
theorem inverse_braiding
    (X Y : A) [IsIso (Functor.LaxMonoidal.μ F X Y)]
    [IsIso (Functor.LaxMonoidal.μ F Y X)] :
    inv (Functor.LaxMonoidal.μ F X Y) ≫ (β_ (F.obj X) (F.obj Y)).hom =
      F.map (β_ X Y).hom ≫ inv (Functor.LaxMonoidal.μ F Y X) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F X Y)).1
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [Functor.LaxBraided.braided (F := F), Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- Transport of a lax braided structure uses the same conjugated tensorator. -/
@[instance_reducible]
def laxBraidedOfIso {G : A ⥤ B} (e : F ≅ G) : G.LaxBraided where
  toLaxMonoidal := Functor.LaxMonoidal.ofIso e
  braided X Y := by
    change ((e.inv.app X ⊗ₘ e.inv.app Y) ≫
      Functor.LaxMonoidal.μ F X Y ≫ e.hom.app _) ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ ((e.inv.app Y ⊗ₘ e.inv.app X) ≫
        Functor.LaxMonoidal.μ F Y X ≫ e.hom.app _)
    simp only [Category.assoc, ← e.hom.naturality,
      ← BraidedCategory.braiding_naturality_assoc]
    rw [Functor.LaxBraided.braided_assoc]
end BraidedTensorator


section AcyclicTensor
variable {A : Type*} [Category* A] [Abelian A] [HasColimitsOfSize.{0, 0} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
  [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
  [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

/-- The Koszul involution descends to homotopy classes. -/
@[instance_reducible]
def homotopySymmetric : SymmetricCategory (HomotopyCategory A (.up ℤ)) where
  toBraidedCategory := inferInstance
  symmetry X Y := by
    obtain ⟨X, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨Y, rfl⟩ := Y.quotient_obj_surjective
    exact ((HomotopyCategory.quotient _ _).map_comp _ _).symm.trans
      (((HomotopyCategory.quotient _ _).congr_map (complex_symmetry X Y)).trans
        ((HomotopyCategory.quotient _ _).map_id _))

/-- The acyclicity test implies categorical K-flatness in the homotopy category. -/
theorem kFlat_of_acyclic (P : CochainComplex A ℤ)
    (hP : ∀ Z : CochainComplex A ℤ, Z.Acyclic → (Z ⊗ P).Acyclic) :
    (HomotopyCategory.quasiIso A (.up ℤ)).kFlat
      ((HomotopyCategory.quotient _ _).obj P) := by
  apply (HomotopyCategory.kFlat_iff_preserves_acyclic _).2
  intro Z hZ
  obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
  have hZ' :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).1 hZ
  have hp : (Z ⊗ P).Acyclic := hP Z hZ'
  constructor
  · apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
    intro i
    exact (hp i).of_iso (CochainComplex.Monoidal.braiding Z P)
  · exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hp
/-- The homotopy quotient preserves the Koszul braiding. -/
@[instance_reducible]
def quotientLaxBraided : (HomotopyCategory.quotient A (.up ℤ)).LaxBraided where
  toLaxMonoidal := inferInstance
  braided X Y := by
    change 𝟙 _ ≫ (HomotopyCategory.quotient A (.up ℤ)).map (β_ X Y).hom =
      (HomotopyCategory.quotient A (.up ℤ)).map (β_ X Y).hom ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

omit [HasColimitsOfSize.{0, 0} A] [SymmetricCategory A] in
/-- The derived tensorator is invertible if either homotopy representative is K-flat. -/
theorem localization_isIso_mu [HasDerivedCategory.{w} A]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso A (.up ℤ))]
    [(HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]
    (P L : CochainComplex A ℤ)
    (h : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat
        ((HomotopyCategory.quotient _ _).obj P) ∨
      (HomotopyCategory.quasiIso A (.up ℤ)).kFlat
        ((HomotopyCategory.quotient _ _).obj L)) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{w} P L) := by
  rcases h with hP | hL
  · have := DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
      DerivedCategory.Qh.{w} (HomotopyCategory.quasiIso A (.up ℤ))
      ((HomotopyCategory.quotient _ _).obj P)
      ((HomotopyCategory.quotient _ _).obj L) hP
    change IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj L)) at this
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ _) ≫ _)
    infer_instance
  · have := DerivedMonoidal.isIso_counit_app_app_of_kFlat_right
      DerivedCategory.Qh.{w} (HomotopyCategory.quasiIso A (.up ℤ))
      ((HomotopyCategory.quotient _ _).obj P)
      ((HomotopyCategory.quotient _ _).obj L) hL
    change IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj L)) at this
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ _) ≫ _)
    infer_instance


omit [HasColimitsOfSize.{0, 0} A] [SymmetricCategory A] in
/-- The native derived localization has an invertible unit comparison. -/
theorem localization_isIso_ε [HasDerivedCategory.{w} A]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso A (.up ℤ))] :
    IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q.{w} (C := A))) := by
  have : IsIso (Functor.LaxMonoidal.ε
      (DerivedCategory.Qh.{w} (C := A))) := by
    change IsIso (𝟙 _)
    infer_instance
  change IsIso ((Functor.LaxMonoidal.ε DerivedCategory.Qh ≫
    DerivedCategory.Qh.map (Functor.LaxMonoidal.ε (HomotopyCategory.quotient _ _))) ≫ _)
  infer_instance


section DerivedSymmetric
variable [HasDerivedCategory.{w} A]
  [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso A (.up ℤ))]
  [(HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]

/-- Symmetry of complexes and homotopy classes descends to the derived category. -/
@[instance_reducible]
def derivedSymmetric : SymmetricCategory (DerivedCategory A) := by
  let H := HomotopyCategory A (.up ℤ)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let L : H ⥤ DerivedCategory A := DerivedCategory.Qh
  let : SymmetricCategory H := homotopySymmetric
  exact localizedSymmetric L W


local instance : SymmetricCategory (DerivedCategory A) := derivedSymmetric

/-- The derived localization preserves the braiding with its canonical lax tensorator. -/
@[instance_reducible]
def localizationLaxBraided : (DerivedCategory.Q : CochainComplex A ℤ ⥤
    DerivedCategory A).LaxBraided := by
  let H := HomotopyCategory A (.up ℤ)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let L : H ⥤ DerivedCategory A := DerivedCategory.Qh
  let : SymmetricCategory H := homotopySymmetric
  let : L.LaxBraided :=
    { toLaxMonoidal := inferInstance
      braided X Y := by
        change Functor.LaxMonoidal.μ L X Y ≫ L.map (β_ X Y).hom =
          (DerivedMonoidal.braiding' L W (L.obj X) (L.obj Y)).hom ≫
            Functor.LaxMonoidal.μ L Y X
        exact (DerivedMonoidal.braiding_hom_μ L W X Y).symm }
  let : (HomotopyCategory.quotient A (.up ℤ)).LaxBraided :=
    quotientLaxBraided
  exact laxBraidedOfIso _ (DerivedCategory.quotientCompQhIso _)

end DerivedSymmetric

end AcyclicTensor


variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

abbrev Modules := SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)

local instance moduleMonoidal : MonoidalCategory (Modules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesMonoidal R
local instance moduleSymmetric : SymmetricCategory (Modules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesSymmetric R
local instance modulePreadditive : MonoidalPreadditive (Modules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesPreadditive R
local instance moduleClosed : MonoidalClosed (Modules.{c, v, u} J R) :=
  (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
local instance moduleGrothendieck : IsGrothendieckAbelian.{max c v u} (Modules.{c, v, u} J R) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
    J R).1
local instance moduleFlat : Abelian.HasFunctorialFlatResolution (Modules.{c, v, u} J R) :=
  SheafOfModules.hasFunctorialFlatResolution_kfi R
local instance countableColimits : HasColimitsOfSize.{0, 0} (Modules.{c, v, u} J R) :=
  hasColimitsOfSizeShrink.{0, 0, max c v u, max c v u} (Modules.{c, v, u} J R)
local instance tensorLeftColimits (M : Modules.{c, v, u} J R) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  SheafOfModules.cochainTensorLeftPreservesColimits R M
local instance tensorRightColimits (M : Modules.{c, v, u} J R) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  SheafOfModules.cochainTensorRightPreservesColimits R M

variable [HasDerivedCategory.{w} (Modules.{c, v, u} J R)]

/-- The usual derived monoidal structure, obtained from functorial flat covers.
Source: Stacks Project, Tags 06YS and 0FPT. -/
@[instance_reducible]
def monoidal : MonoidalCategory (DerivedCategory (Modules.{c, v, u} J R)) := inferInstance

local instance : MonoidalCategory (DerivedCategory (Modules.{c, v, u} J R)) :=
  monoidal.{c, v, u, w} J R

/-- The localization's canonical lax comparison, from derived tensor to total tensor.
Source: Stacks Project, Tag 06YT. -/
@[instance_reducible]
def lax : (DerivedCategory.Q : CochainComplex (Modules.{c, v, u} J R) ℤ ⥤ _).LaxMonoidal :=
  inferInstance

omit [HasDerivedCategory.{w} (Modules.{c, v, u} J R)] in
/-- The native complex tensor is precisely the recorded total tensor.
Source: Stacks Project, Tag 06YN. -/
theorem totalTensor_eq (P L : CochainComplex (Modules.{c, v, u} J R) ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj (P, L) = P ⊗ L := by
  rfl

omit [HasDerivedCategory.{w} (Modules.{c, v, u} J R)] in
/-- The acyclicity definition of K-flatness implies the native two-sided predicate.
Source: Stacks Project, Tag 06YT. -/
theorem kFlat (P : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    (HomotopyCategory.quasiIso (Modules.{c, v, u} J R) (.up ℤ)).kFlat
      ((HomotopyCategory.quotient _ _).obj P) := by
  exact kFlat_of_acyclic P (fun Z hZ ↦ hP Z hZ)

local instance : (DerivedCategory.Q : CochainComplex (Modules.{c, v, u} J R) ℤ ⥤
    DerivedCategory (Modules.{c, v, u} J R)).LaxMonoidal := lax.{c, v, u, w} J R

/-- The native tensor comparison is invertible when either complex is K-flat.
Source: Stacks Project, Tag 06YT. -/
theorem isIso_mu (P L : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (h : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∨
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{w} P L) := by
  exact localization_isIso_mu P L
    (h.imp (kFlat.{c, v, u} J R P) (kFlat.{c, v, u} J R L))

/-- The inverse native lax comparison is the one-K-flat tensor model.
Source: Stacks Project, Tag 06YT. -/
def tensorIso (P L : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (h : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∨
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L) :
    DerivedCategory.Q.{w}.obj ((coefficientTotalTensor.{u, c, v} J R).obj (P, L)) ≅
      @tensorObj (DerivedCategory (Modules.{c, v, u} J R)) _
      (monoidal.{c, v, u, w} J R).toMonoidalCategoryStruct
        (DerivedCategory.Q.{w}.obj P) (DerivedCategory.Q.{w}.obj L) :=
  have := isIso_mu.{c, v, u, w} J R P L h
  (asIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{w} P L)).symm

/-- The comparison is the inverse of the native lax tensorator. -/
theorem tensorIso_hom (P L : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (h : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∨
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L)
    [IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{w} P L)] :
    (tensorIso.{c, v, u, w} J R P L h).hom =
      inv (Functor.LaxMonoidal.μ DerivedCategory.Q.{w} P L) := rfl

/-- Naturality of the one-K-flat comparison for all chain maps between allowed pairs.
Source: Stacks Project, Tag 06YT. -/
theorem tensorIso_naturality
    (P L P' L' : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (h : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∨
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L)
    (h' : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P' ∨
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L')
    (f : P ⟶ P') (g : L ⟶ L') :
    DerivedCategory.Q.{w}.map ((coefficientTotalTensor.{u, c, v} J R).map (f, g)) ≫
        (tensorIso.{c, v, u, w} J R P' L' h').hom =
      (tensorIso.{c, v, u, w} J R P L h).hom ≫
        (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) := by
  have := isIso_mu.{c, v, u, w} J R P L h
  have := isIso_mu.{c, v, u, w} J R P' L' h'
  change DerivedCategory.Q.map ((f ▷ L) ≫ (P' ◁ g)) ≫
      inv (Functor.LaxMonoidal.μ DerivedCategory.Q P' L') =
    inv (Functor.LaxMonoidal.μ DerivedCategory.Q P L) ≫
      (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g)
  rw [← tensorHom_def]
  exact inverse_naturality DerivedCategory.Q f g

/-- The simultaneous K-flat representative comparison, natural in both variables.
Source: Stacks Project, Tag 06YT. -/
def comparison :
    ((coefficientKFlatInclusion.{u, c, v} J R).prod
      (coefficientKFlatInclusion.{u, c, v} J R)) ⋙ coefficientTotalTensor.{u, c, v} J R ⋙
        DerivedCategory.Q.{w} ≅
    ((coefficientKFlatInclusion.{u, c, v} J R ⋙ DerivedCategory.Q).prod
      (coefficientKFlatInclusion.{u, c, v} J R ⋙ DerivedCategory.Q)) ⋙
        @tensor (DerivedCategory (Modules.{c, v, u} J R)) _ (monoidal.{c, v, u, w} J R) :=
  NatIso.ofComponents
    (fun X ↦ tensorIso.{c, v, u, w} J R X.1.obj X.2.obj (Or.inl X.1.property))
    (fun f ↦ tensorIso_naturality.{c, v, u, w} J R _ _ _ _ _ _ f.1.hom f.2.hom)

/-- The simultaneous comparison has the specified one-K-flat components. -/
theorem comparison_app
    (P L : ObjectProperty.FullSubcategory
      (CochainComplex.IsKFlatIndependentCoefficients
        (J := J) (R := R) : ObjectProperty (CochainComplex (Modules.{c, v, u} J R) ℤ))) :
    (comparison.{c, v, u, w} J R).app (P, L) =
      tensorIso.{c, v, u, w} J R P.obj L.obj (Or.inl P.property) := rfl

/-- The Koszul symmetry is an involution after localization.
Source: Stacks Project, Tag 0FPT. -/
@[instance_reducible]
def symmetric : SymmetricCategory (DerivedCategory (Modules.{c, v, u} J R)) := by
  exact derivedSymmetric (A := Modules.{c, v, u} J R)


local instance : SymmetricCategory (DerivedCategory (Modules.{c, v, u} J R)) :=
  symmetric.{c, v, u, w} J R

/-- Localization preserves the Koszul braiding with its fixed lax tensorator.
Source: Stacks Project, Tag 0FPT. -/
@[instance_reducible]
def laxBraided : (DerivedCategory.Q : CochainComplex (Modules.{c, v, u} J R) ℤ ⥤
    DerivedCategory (Modules.{c, v, u} J R)).LaxBraided := by
  exact localizationLaxBraided (A := Modules.{c, v, u} J R)

/-- The comparison intertwines the native braidings. -/
theorem symmetry_square (P Q : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q) :
    (tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
        (β_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map (β_ P Q).hom ≫
        (tensorIso.{c, v, u, w} J R Q P (Or.inl hQ)).hom := by
  let : (DerivedCategory.Q : CochainComplex (Modules.{c, v, u} J R) ℤ ⥤
      DerivedCategory (Modules.{c, v, u} J R)).LaxBraided := laxBraided.{c, v, u, w} J R
  have := isIso_mu.{c, v, u, w} J R P Q (Or.inl hP)
  have := isIso_mu.{c, v, u, w} J R Q P (Or.inl hQ)
  change inv (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫ _ =
    _ ≫ inv (Functor.LaxMonoidal.μ DerivedCategory.Q Q P)
  exact inverse_braiding DerivedCategory.Q P Q

/-- The unit comparison of localization is invertible. -/
theorem isIso_ε : IsIso (Functor.LaxMonoidal.ε
    (DerivedCategory.Q.{w} (C := Modules.{c, v, u} J R))) := by
  exact localization_isIso_ε (A := Modules.{c, v, u} J R)

/-- The localization identifies the derived unit with the ring in degree zero.
Source: Stacks Project, Tag 0FPT. -/
def unitIso : 𝟙_ (DerivedCategory (Modules.{c, v, u} J R)) ≅
    DerivedCategory.Q.{w}.obj (𝟙_ (CochainComplex (Modules.{c, v, u} J R) ℤ)) := by
  have := isIso_ε.{c, v, u, w} J R
  exact asIso (Functor.LaxMonoidal.ε DerivedCategory.Q.{w})


/-- The inverse unit comparison is the inverse of the lax unit map. -/
theorem unitIso_inv [IsIso (Functor.LaxMonoidal.ε
    (DerivedCategory.Q.{w} (C := Modules.{c, v, u} J R)))] :
    (unitIso.{c, v, u, w} J R).inv =
      inv (Functor.LaxMonoidal.ε DerivedCategory.Q.{w}) := rfl


/-- The fixed tensor comparison preserves reassociation. -/
theorem associator_square (P Q N : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
    (hN : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) N) :
    (tensorIso.{c, v, u, w} J R (P ⊗ Q) N (Or.inr hN)).hom ≫
        ((tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ⊗ₘ 𝟙 _) ≫
        (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj N)).hom =
      DerivedCategory.Q.map (α_ P Q N).hom ≫
        (tensorIso.{c, v, u, w} J R P (Q ⊗ N) (Or.inl hP)).hom ≫
        (𝟙 _ ⊗ₘ (tensorIso.{c, v, u, w} J R Q N (Or.inl hQ)).hom) := by
  have := isIso_mu.{c, v, u, w} J R P Q (Or.inl hP)
  have := isIso_mu.{c, v, u, w} J R Q N (Or.inl hQ)
  have := isIso_mu.{c, v, u, w} J R (P ⊗ Q) N (Or.inr hN)
  have := isIso_mu.{c, v, u, w} J R P (Q ⊗ N) (Or.inl hP)
  exact inverse_associativity_tensor DerivedCategory.Q P Q N

/-- The fixed tensor comparison preserves the left unit constraint. -/
theorem leftUnitor_square (P : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    (tensorIso.{c, v, u, w} J R (𝟙_ _) P (Or.inr hP)).hom ≫
      ((unitIso.{c, v, u, w} J R).inv ⊗ₘ 𝟙 _) ≫
        (λ_ (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map (λ_ P).hom := by
  have := isIso_mu.{c, v, u, w} J R (𝟙_ _) P (Or.inr hP)
  have := isIso_ε.{c, v, u, w} J R
  exact inverse_leftUnitor_tensor DerivedCategory.Q P

/-- The fixed tensor comparison preserves the right unit constraint. -/
theorem rightUnitor_square (P : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    (tensorIso.{c, v, u, w} J R P (𝟙_ _) (Or.inl hP)).hom ≫
      (𝟙 _ ⊗ₘ (unitIso.{c, v, u, w} J R).inv) ≫
        (ρ_ (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map (ρ_ P).hom := by
  have := isIso_mu.{c, v, u, w} J R P (𝟙_ _) (Or.inl hP)
  have := isIso_ε.{c, v, u, w} J R
  exact inverse_rightUnitor_tensor DerivedCategory.Q P

end CategoryTheory.RingedDerivedNative
