/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionData
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-! # Multiplication units for derived coefficient extension

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E and 07A6
(blueprint: lem-pur-coefficient-scalar-units).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped ChangeOfRings
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}

variable {p : Scalars.{c, v, r} J}
  (n : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) p)




private theorem termwise_commShift
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (t : F ⟶ G) :
    NatTrans.CommShift (NatTrans.mapHomologicalComplex t (.up ℤ)) ℤ := by
  constructor
  intro n
  ext K i
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    NatTrans.mapHomologicalComplex_app_f, CochainComplex.shiftFunctor_map_f',
    CochainComplex.shiftFunctor_obj_X', Category.id_comp, Category.comp_id]

private theorem homotopy_commShift
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (t : F ⟶ G) :
    NatTrans.CommShift (NatTrans.mapHomotopyCategory t (.up ℤ)) ℤ := by
  have := termwise_commShift t
  have he : whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (NatTrans.mapHomotopyCategory t (.up ℤ)) =
      (F.mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ))
          (HomotopyCategory.quotient B (.up ℤ)) ≫
        (G.mapHomotopyCategoryFactors (.up ℤ)).inv := by
    ext K
    simp only [Functor.comp_obj, Functor.whiskerLeft_app,
      NatTrans.mapHomotopyCategory_app, NatTrans.comp_app, Functor.whiskerRight_app]
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    erw [Category.id_comp, Category.comp_id]
    rfl
  have : NatTrans.CommShift (whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (NatTrans.mapHomotopyCategory t (.up ℤ))) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient A (.up ℤ))
    (fun K ↦ ⟨_, 𝟙 _, (HomotopyCategory.quotient_obj_surjective K).choose_spec ▸
      inferInstance⟩)

private theorem homotopyId_commShift
    {A : Type*} [Category A] [Preadditive A] :
    NatTrans.CommShift (Functor.mapHomotopyCategoryIdIso A (.up ℤ)).hom ℤ := by
  have hc : NatTrans.CommShift (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom ℤ := by
    constructor
    intro n
    ext K i
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Functor.commShiftIso_id_hom_app, HomologicalComplex.id_f,
      CochainComplex.shiftFunctor_map_f', mapHomologicalComplexIdIso_hom_app_f,
      Category.id_comp]
    erw [Category.id_comp]
    rfl
  have he : whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (Functor.mapHomotopyCategoryIdIso A (.up ℤ)).hom =
      ((𝟭 A).mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        whiskerRight (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom
          (HomotopyCategory.quotient A (.up ℤ)) ≫
        (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv := by
    ext K
    simp only [Functor.comp_obj, Functor.id_obj, Functor.whiskerLeft_app,
      mapHomotopyCategoryIdIso_hom_app, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Category.comp_id]
    erw [Category.id_comp]
  have : NatTrans.CommShift (whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (Functor.mapHomotopyCategoryIdIso A (.up ℤ)).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient A (.up ℤ))
    (fun K ↦ ⟨_, 𝟙 _, (HomotopyCategory.quotient_obj_surjective K).choose_spec ▸
      inferInstance⟩)

private def restrictionUnit (R : Sheaf J CommRingCat.{r}) :
    _root_.SheafOfModules.SuccessiveDerivedQuotient.restriction.{c, v, r} (𝟙 R) ≅ 𝟭 (Mod J R) :=
  NatIso.ofComponents (fun M ↦ {
    hom := { val := {
      app := fun U ↦ ModuleCat.ofHom {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    inv := { val := {
      app := fun U ↦ ModuleCat.ofHom {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } } }) (by intros; ext; rfl)

private def ordinaryUnit (R : Sheaf J CommRingCat.{r}) :
    (p (𝟙 R)).ordinary ≅ 𝟭 (Mod J R) := by
  let a := (n.ordinaryAdjunction (𝟙 R)).ofNatIsoRight (restrictionUnit R)
  exact a.leftAdjointUniq (Adjunction.id)

private theorem sectionTensor_smul
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Mod J R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    SuccessiveDerivedQuotient.sectionTensor (p a) M U s x =
      s • SuccessiveDerivedQuotient.sectionTensor (p a) M U 1 x := by
  let q0 : (changeOfRingsPresheaf.{v, c, r} a M).obj U ⟶
      (ModuleCat.restrictScalars (RingHom.id (S.obj.obj U))).obj
        ((changeOfRings.{v, c, r} a M).val.obj U) :=
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
      (𝟙 _)).unit.app (changeOfRingsPresheaf.{v, c, r} a M)).app U
  let q : (changeOfRingsPresheaf.{v, c, r} a M).obj U ⟶
      ((p a).ordinary.obj M).val.obj U :=
    q0 ≫ (ModuleCat.restrictScalarsId (S.obj.obj U)).hom.app _ ≫
      (eqToHom ((p a).obj_eq M).symm).val.app U
  have hq (t : S.obj.obj U) :
      q (t ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) =
        SuccessiveDerivedQuotient.sectionTensor (p a) M U t x := by rfl
  rw [← hq, ← hq]
  have ht : s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x =
      s • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) := by
    change s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x =
      (s * 1) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x
    rw [mul_one]
  rw [ht]
  exact q.hom.map_smul s _

private theorem ordinaryUnit_one (R : Sheaf J CommRingCat.{r})
    (M : Mod J R) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((ordinaryUnit n R).hom.app M).val.app U
      (SuccessiveDerivedQuotient.sectionTensor (p (𝟙 R)) M U 1 x) = x := by
  let a := (n.ordinaryAdjunction (𝟙 R)).ofNatIsoRight (restrictionUnit R)
  have h := Adjunction.unit_leftAdjointUniq_hom_app a (Adjunction.id) M
  have he := congrArg (fun f ↦ f.val.app U x) h
  change ((ordinaryUnit n R).hom.app M).val.app U
    (((n.ordinaryAdjunction (𝟙 R)).unit.app M).val.app U x) = x at he
  rw [n.ordinary_unit] at he
  exact he

private theorem ordinaryUnit_multiplication (R : Sheaf J CommRingCat.{r})
    (M : Mod J R) (U : Cᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U) :
    ((ordinaryUnit n R).hom.app M).val.app U
      (SuccessiveDerivedQuotient.sectionTensor (p (𝟙 R)) M U s x) = s • x := by
  rw [sectionTensor_smul, _root_.map_smul, ordinaryUnit_one]

private def homotopyUnit (R : Sheaf J CommRingCat.{r}) :
    (p (𝟙 R)).ordinary.mapHomotopyCategory (.up ℤ) ≅
      𝟭 (HomotopyCategory (Mod J R) (.up ℤ)) :=
  { hom := NatTrans.mapHomotopyCategory (ordinaryUnit n R).hom (.up ℤ)
    inv := NatTrans.mapHomotopyCategory (ordinaryUnit n R).inv (.up ℤ)
    hom_inv_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] } ≪≫
    Functor.mapHomotopyCategoryIdIso (Mod J R) (.up ℤ)

private def homotopyUnitQ (R : Sheaf J CommRingCat.{r}) :
    (p (𝟙 R)).ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      DerivedCategory.Qh :=
  isoWhiskerRight (homotopyUnit n R) DerivedCategory.Qh ≪≫
    Functor.leftUnitor DerivedCategory.Qh

private def derivedUnit (R : Sheaf J CommRingCat.{r}) :
    (p (𝟙 R)).derived ≅ 𝟭 (D J R) := by
  let a : DerivedCategory.Qh ⋙ 𝟭 (D J R) ≅ DerivedCategory.Qh :=
    Functor.rightUnitor DerivedCategory.Qh
  let := (p (𝟙 R)).universal
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Mod J R) (.up ℤ)) (𝟭 (D J R)) a
  exact Functor.leftDerivedNatIso _ _ (p (𝟙 R)).counit a.hom
    (HomotopyCategory.quasiIso (Mod J R) (.up ℤ)) (homotopyUnitQ n R)

private theorem derivedUnit_app_homotopy (R : Sheaf J CommRingCat.{r})
    (H : HomotopyCategory (Mod J R) (.up ℤ)) :
    (derivedUnit n R).hom.app (DerivedCategory.Qh.obj H) =
      (p (𝟙 R)).counit.app H ≫
        DerivedCategory.Qh.map ((homotopyUnit n R).hom.app H) := by
  let a : DerivedCategory.Qh ⋙ 𝟭 (D J R) ≅ DerivedCategory.Qh :=
    Functor.rightUnitor DerivedCategory.Qh
  let := (p (𝟙 R)).universal
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Mod J R) (.up ℤ)) (𝟭 (D J R)) a
  have h := Functor.leftDerivedNatTrans_app (p (𝟙 R)).derived (𝟭 (D J R))
    (p (𝟙 R)).counit a.hom (HomotopyCategory.quasiIso (Mod J R) (.up ℤ))
    (homotopyUnitQ n R).hom H
  change (derivedUnit n R).hom.app (DerivedCategory.Qh.obj H) ≫ 𝟙 _ = _ at h
  change (derivedUnit n R).hom.app (DerivedCategory.Qh.obj H) ≫ 𝟙 _ =
    (p (𝟙 R)).counit.app H ≫
      (DerivedCategory.Qh.map ((homotopyUnit n R).hom.app H) ≫ 𝟙 _) at h
  simpa only [Category.comp_id] using h

private theorem derivedUnit_commShift
    [scalar : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
      (p a).derived.CommShift ℤ]
    (canonical : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
      NatTrans.CommShift (p a).counit ℤ) (R : Sheaf J CommRingCat.{r}) :
    NatTrans.CommShift (derivedUnit n R).hom ℤ := by
  have := homotopy_commShift (ordinaryUnit n R).hom
  have := homotopyId_commShift (A := Mod J R)
  have : NatTrans.CommShift (homotopyUnit n R).hom ℤ := by
    dsimp only [homotopyUnit, Iso.trans_hom]
    infer_instance
  have : NatTrans.CommShift (homotopyUnitQ n R).hom ℤ := by
    change NatTrans.CommShift
      (whiskerRight (homotopyUnit n R).hom DerivedCategory.Qh ≫
        (Functor.leftUnitor _).hom) ℤ
    infer_instance
  have := canonical (𝟙 R)
  have he : whiskerLeft DerivedCategory.Qh (derivedUnit n R).hom =
      (p (𝟙 R)).counit ≫ (homotopyUnitQ n R).hom ≫
        (Functor.rightUnitor DerivedCategory.Qh).inv := by
    ext H
    change (derivedUnit n R).hom.app (DerivedCategory.Qh.obj H) =
      (p (𝟙 R)).counit.app H ≫
        (DerivedCategory.Qh.map ((homotopyUnit n R).hom.app H) ≫ 𝟙 _) ≫ 𝟙 _
    simp only [Category.comp_id]
    exact derivedUnit_app_homotopy n R H
  have : NatTrans.CommShift
      (whiskerLeft DerivedCategory.Qh (derivedUnit n R).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun H ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso H).inv, inferInstance⟩)

private theorem derivedUnit_representative (R : Sheaf J CommRingCat.{r})
    (P : CochainComplex (Mod J R) ℤ) :
    (derivedUnit n R).hom.app (DerivedCategory.Q.obj P) =
      computation (p (𝟙 R)) P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (ordinaryUnit n R).hom (.up ℤ)).app P) := by
  have hn := (derivedUnit n R).hom.naturality
    ((DerivedCategory.quotientCompQhIso (Mod J R)).inv.app P)
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn
  have hf : ((p (𝟙 R)).ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom.app P =
      𝟙 _ := rfl
  have hu : (homotopyUnit n R).hom.app
      ((HomotopyCategory.quotient (Mod J R) (.up ℤ)).obj P) =
        (HomotopyCategory.quotient (Mod J R) (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (ordinaryUnit n R).hom (.up ℤ)).app P) := by
    simp only [homotopyUnit, Iso.trans_hom, NatTrans.comp_app,
      Functor.mapHomotopyCategoryIdIso_hom_app_eq_id]
    rfl
  calc
    _ = (p (𝟙 R)).derived.map
          ((DerivedCategory.quotientCompQhIso (Mod J R)).inv.app P) ≫
        (derivedUnit n R).hom.app
          ((HomotopyCategory.quotient (Mod J R) (.up ℤ) ⋙ DerivedCategory.Qh).obj P) ≫
        (DerivedCategory.quotientCompQhIso (Mod J R)).hom.app P := by
      dsimp only [Functor.comp_obj]
      rw [reassoc_of% hn]
      simp only [Iso.inv_hom_id_app, Category.comp_id]
    _ = _ := by
      dsimp only [Functor.comp_obj]
      erw [derivedUnit_app_homotopy n R
        ((HomotopyCategory.quotient (Mod J R) (.up ℤ)).obj P), hu]
      dsimp only [computation, derivedPullbackComplexComparison]
      erw [hf, DerivedCategory.Qh.map_id]
      simp only [Category.assoc]
      erw [DerivedCategory.quotientCompQhIso_hom_naturality]

include n

/-- Scalar extension by the identity has the canonical multiplication unit, both
ordinarily and on derived representatives, compatibly with normalized shifts.

Source: Stacks Project, Modules on Sites, Tag 03EL; Cohomology on Sites, Tag 0D6D
(blueprint: lem-pur-coefficient-scalar-units).

Proof: restriction along the identity is canonically the identity, sectionwise.
Uniqueness of left adjoints gives the ordinary unit isomorphism. The normalized
adjunction unit sends x to 1 tensor x; its triangle equation forces multiplication
on that generator, and linearity gives s tensor x ↦ s • x. Map this isomorphism to
homotopy categories and localize its comparison with Qh. The identity derived
functor is its own left derived functor. Uniqueness of left derived functors
therefore gives the derived unit, and its counit equation, transported along the
quotient/Qh comparison, gives precisely the required complex representative.
This argument works on every complex; the stated K-flat hypotheses are unnecessary.
The termwise ordinary unit commutes with shifts degree by degree. Descend this
compatibility through the homotopy quotient, then whisker by Qh. The universal
counit commutes with the prescribed scalar shifts, so the computation equation
gives compatibility for the derived unit after precomposition by Qh. Every derived
object is isomorphic to an object in the image of Qh, so compatibility descends. -/
theorem coefficientScalarUnits
    [scalar : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
      (p a).derived.CommShift ℤ]
    (canonical : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
      NatTrans.CommShift (p a).counit ℤ) :
    ∃ u : ScalarUnits (p := p),
      ∀ R : Sheaf J CommRingCat.{r}, NatTrans.CommShift (u.derived R).hom ℤ := by
  refine ⟨{
    ordinary := ordinaryUnit n
    multiplication := ordinaryUnit_multiplication n
    derived := derivedUnit n
    representative := fun R P _ _ ↦ derivedUnit_representative n R P }, ?_⟩
  exact fun R ↦ derivedUnit_commShift n canonical R

end SheafOfModules.RingedCoefficientProjection
