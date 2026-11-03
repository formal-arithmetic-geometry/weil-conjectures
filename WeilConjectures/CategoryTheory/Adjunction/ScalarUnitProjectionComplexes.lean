/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ScalarClosedProjectionData
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal

/-! # The scalar-unit projection on cochain complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomologicalComplex
namespace CategoryTheory.Adjunction

private def projectionNat
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {U : D ⥤ C} [F.Monoidal] (adj : F ⊣ U) :
    tensorRight (U.obj (𝟙_ D)) ⟶ F ⋙ U where
  app := scalarUnitProjection adj
  naturality K L f := by
    change f ▷ U.obj (𝟙_ D) ≫ scalarUnitProjection adj L =
      scalarUnitProjection adj K ≫ U.map (F.map f)
    apply (adj.homEquiv _ _).symm.injective
    rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm]
    dsimp only [scalarUnitProjection]
    erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
    rw [← whisker_exchange_assoc]
    dsimp only [Functor.id_obj]
    simp only [Category.assoc, rightUnitor_naturality]

section
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v} D]
  {F : C ⥤ D} {U : D ⥤ C} [F.Monoidal] [F.Additive] [U.Additive]
  [F.IsLeftAdjoint]
  (adj : F ⊣ U)

omit [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
  [MonoidalClosed C] [IsGrothendieckAbelian.{v} C] [F.Monoidal] [F.IsLeftAdjoint] in
private theorem single_counit :
    (F.mapHomologicalComplex (.up ℤ)).map
        ((singleMapHomologicalComplex U (.up ℤ) 0).inv.app (𝟙_ D)) ≫
      (adj.mapHomologicalComplex (.up ℤ)).counit.app (𝟙_ _) =
    (singleMapHomologicalComplex F (.up ℤ) 0).hom.app (U.obj (𝟙_ D)) ≫
      (single D (.up ℤ) 0).map (adj.counit.app (𝟙_ D)) := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp only [comp_f, Functor.mapHomologicalComplex_map_f,
      singleMapHomologicalComplex_inv_app_self, singleMapHomologicalComplex_hom_app_self,
      mapHomologicalComplex_counit_app_f, single_map_f_self, Functor.map_comp,
      Category.assoc]
    erw [adj.counit_naturality]
    simp
  · exact (F.map_isZero (isZero_single_obj_X (.up ℤ) 0 _ i hi)).eq_of_src _ _

private theorem single_rightUnitor (P : CochainComplex D ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (𝟙_ D) P).inv ≫
      (ρ_ P).hom =
    (NatTrans.mapHomologicalComplex (rightUnitorNatIso D).hom (.up ℤ)).app P := by
  have : IsIso ((NatTrans.mapHomologicalComplex (rightUnitorNatIso D).inv
      (.up ℤ)).app P) :=
    inferInstanceAs (IsIso
      ((NatIso.mapHomologicalComplex (rightUnitorNatIso D) (.up ℤ)).inv.app P))
  apply (cancel_mono
    ((NatTrans.mapHomologicalComplex (rightUnitorNatIso D).inv (.up ℤ)).app P)).1
  have h : (ρ_ P).inv ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (𝟙_ D) P).hom =
      (NatTrans.mapHomologicalComplex (rightUnitorNatIso D).inv (.up ℤ)).app P := by
    ext i : 1
    change (HomologicalComplex.rightUnitor' P).inv i ≫ _ = _
    rw [HomologicalComplex.rightUnitor'_inv]
    have hj := congrArg (fun f ↦ f.f i)
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (𝟙_ D) P).inv_hom_id
    rw [comp_f, id_f, CochainComplex.mapBifunctorSingle₂Iso_inv_f] at hj
    simp only [Category.assoc]
    change (ρ_ (P.X i)).inv ≫ _ = (ρ_ (P.X i)).inv
    calc
      _ = (ρ_ (P.X i)).inv ≫
          ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (𝟙_ D) P).inv ≫
            (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (𝟙_ D) P).hom).f i := by
        rw [comp_f, CochainComplex.mapBifunctorSingle₂Iso_inv_f]
        simp only [Category.assoc]
        rfl
      _ = _ := by
        rw [Iso.inv_hom_id, id_f]
        exact Category.comp_id _
  have hi := congr_app
    (NatIso.mapHomologicalComplex (rightUnitorNatIso D) (.up ℤ)).hom_inv_id P
  dsimp only [NatTrans.comp_app, NatTrans.id_app] at hi
  erw [hi]
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]

/-- The canonical scalar-unit projection on complexes is computed degreewise.
Source: Stacks 07A4; the cochain tensor/direct-sum construction.
Proof: identify tensoring with a complex concentrated in degree zero with termwise
 tensoring. The tensor comparison on those summands is the ordinary tensor
 comparison. The counit is degreewise the ordinary counit, and the unitor is
 degreewise the ordinary unitor. Transposing gives the degreewise projection,
 so an ordinary projection isomorphism remains an isomorphism on complexes.
(blueprint: lem-per-scalar-unit-projection-complexes). -/
theorem scalarUnitProjection_complexes_isIso
    (hp : ∀ M : C, IsIso (scalarUnitProjection adj M)) (P : CochainComplex C ℤ) :
    IsIso (scalarUnitProjection (adj.mapHomologicalComplex (.up ℤ)) P) := by
  let B := U.obj (𝟙_ D)
  let FC := F.mapHomologicalComplex (.up ℤ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let ac := adj.mapHomologicalComplex (.up ℤ)
  let e := (singleMapHomologicalComplex U (.up ℤ) 0).app (𝟙_ D)
  let j := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) B P
  let a := j.inv ≫ P ◁ e.inv
  have h : a ≫ scalarUnitProjection ac P =
      (NatTrans.mapHomologicalComplex (projectionNat adj) (.up ℤ)).app P := by
    apply (ac.homEquiv _ _).symm.injective
    rw [homEquiv_naturality_left_symm]
    dsimp only [scalarUnitProjection]
    erw [Equiv.symm_apply_apply]
    have ht := CochainComplex.mapBifunctorComparison_δNatTrans_single₂ F P B
    let jF := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (F.obj B)
      (FC.obj P)
    let sF := (singleMapHomologicalComplex F (.up ℤ) 0).app B
    change FC.map j.inv ≫ Functor.OplaxMonoidal.δ FC P
      ((single C (.up ℤ) 0).obj B) ≫ FC.obj P ◁ sF.hom ≫ jF.hom = _ at ht
    have ht' : FC.map j.inv ≫ Functor.OplaxMonoidal.δ FC P
        ((single C (.up ℤ) 0).obj B) ≫ FC.obj P ◁ sF.hom =
      (NatTrans.mapHomologicalComplex (Functor.OplaxMonoidal.δRightNatTrans F B)
        (.up ℤ)).app P ≫ jF.inv := by
      apply (cancel_mono jF.hom).1
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ht
    have hc := single_counit adj
    dsimp only [a]
    rw [FC.map_comp]
    simp only [Category.assoc]
    erw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
    erw [← whiskerLeft_comp_assoc, hc]
    simp only [whiskerLeft_comp, Category.assoc]
    erw [reassoc_of% ht']
    have hn := CochainComplex.mapBifunctorSingle₂Iso_inv_naturality₂
      (curriedTensor D) (adj.counit.app (𝟙_ D)) (FC.obj P)
    change (NatTrans.mapHomologicalComplex
      ((tensoringRight D).map (adj.counit.app (𝟙_ D))) (.up ℤ)).app (FC.obj P) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (𝟙_ D) (FC.obj P)).inv =
      jF.inv ≫ FC.obj P ◁ (single D (.up ℤ) 0).map (adj.counit.app (𝟙_ D)) at hn
    rw [← reassoc_of% hn]
    erw [single_rightUnitor (FC.obj P)]
    ext i : 1
    change Functor.OplaxMonoidal.δ F (P.X i) B ≫
      F.obj (P.X i) ◁ adj.counit.app (𝟙_ D) ≫ (ρ_ (F.obj (P.X i))).hom =
      (adj.homEquiv _ _).symm (scalarUnitProjection adj (P.X i))
    exact ((adj.homEquiv _ _).symm_apply_apply _).symm
  have hm : IsIso ((NatTrans.mapHomologicalComplex (projectionNat adj) (.up ℤ)).app P) := by
    have (i : ℤ) : IsIso
        (((NatTrans.mapHomologicalComplex (projectionNat adj) (.up ℤ)).app P).f i) :=
      hp (P.X i)
    exact HomologicalComplex.Hom.isIso_of_components _
  have : IsIso a := by dsimp only [a]; infer_instance
  exact (isIso_comp_left_iff a _).mp (h ▸ hm)

/-- The ordinary scalar projection remains invertible after homotopy localization.
Source and proof: Stacks 07A4; the preceding degreewise projection computation.
The quotient preserves its tensor comparison, adjunction unit and counit, and
right unitor, so it sends the cochain projection to this projection.
(blueprint: lem-per-scalar-unit-projection-complexes). -/
private theorem scalarUnitProjection_homotopy_isIso
    (hp : ∀ M : C, IsIso (scalarUnitProjection adj M))
    (P : HomotopyCategory C (.up ℤ)) :
    IsIso (scalarUnitProjection (adj.mapHomotopyCategory (.up ℤ)) P) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  let qC := HomotopyCategory.quotient C (.up ℤ)
  let qD := HomotopyCategory.quotient D (.up ℤ)
  let ac := adj.mapHomologicalComplex (.up ℤ)
  let ah := adj.mapHomotopyCategory (.up ℤ)
  have ht (K : CochainComplex C ℤ) (N : CochainComplex D ℤ)
      (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ N) :
      ah.homEquiv (qC.obj K) (qD.obj N) (qD.map f) =
        qC.map (ac.homEquiv K N f) := by
    rw [homEquiv_unit, mapHomotopyCategory_unit_app_quotient,
      homEquiv_unit, qC.map_comp]
    rfl
  have he : scalarUnitProjection ah (qC.obj P) =
      qC.map (scalarUnitProjection ac P) := by
    dsimp only [scalarUnitProjection]
    rw [← ht]
    congr 1
    change Functor.OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ))
      (qC.obj P) (qC.obj ((U.mapHomologicalComplex (.up ℤ)).obj (𝟙_ _))) ≫
        qD.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ◁
          ah.counit.app (qD.obj (𝟙_ _)) ≫
        (ρ_ (qD.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))).hom = _
    erw [Functor.mapHomotopyCategory_δ,
      Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app,
      ← Functor.mapCochainComplex_δ]
    rw [mapHomotopyCategory_counit_app_quotient]
    have hu : (ρ_ (qD.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))).hom =
        qD.map (ρ_ ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom :=
      HomotopyCategory.MonoidalCategory.rightUnitor_hom_app _
    erw [hu]
    simp only [qD.map_comp]
    erw [HomotopyCategory.MonoidalCategory.quotient_map_whiskerLeft']
  rw [he]
  have : IsIso (scalarUnitProjection ac P) :=
    scalarUnitProjection_complexes_isIso adj hp P
  infer_instance
end
end CategoryTheory.Adjunction
