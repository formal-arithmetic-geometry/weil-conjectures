/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
/-!
# The derived unit and the classical degree-zero augmentation

Source: Stacks Project, Derived Categories, Tag 05TD, part (3), and the unit
characterization of derived base change
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison).
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {B C : Type*} [Category* B] [Category* C] [Abelian B] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C] [EnoughInjectives B]
  (G : B ⥤ C) [G.Additive]

/-- The unit on an object placed in degree zero, using the single-complex comparisons.

Source: `rightDerivedFunctorPlusUnit` and `mapHomotopyCategoryPlusSingleFunctorQhObjIso`
in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison). -/
noncomputable def rightDerivedPlusSingleUnit (Y : B) :
    (DerivedCategory.Plus.singleFunctor C 0).obj (G.obj Y) ⟶
      G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj Y) :=
  (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 Y).inv ≫
    G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor B 0).obj Y) ≫
    G.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.ι.preimageIso
        (X := (DerivedCategory.Plus.singleFunctor B 0).obj Y)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor B 0).obj Y))
        ((DerivedCategory.singleFunctorIsoCompQ B 0).app Y ≪≫
          (DerivedCategory.quotientCompQhIso B).symm.app _)).inv

/-- Degree-zero homology of the derived unit on a single complex.

Source: the preceding unit and `DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso`
in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`.
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison). -/
noncomputable def rightDerivedPlusSingleUnitHomology (Y : B) :
    G.obj Y ⟶ (DerivedCategory.Plus.homologyFunctor C 0).obj
      (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj Y)) :=
  (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app (G.obj Y) ≫
    (DerivedCategory.Plus.homologyFunctor C 0).map (G.rightDerivedPlusSingleUnit Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The single-complex homology comparison identifies the derived unit with the
classical augmentation.

Source: Stacks Project, Derived Categories, Tag 05TD, part (3), and the definitions of
`homologyRightDerivedFunctorPlusObjSingleFunctorIso` and `toRightDerivedZero`.
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison).

Proof: choose the injective resolution of Y used in both definitions. Naturality of the
right-derived unit along the resolution augmentation identifies the unit on Y[0] with
its map into the resolution followed by the unit on that resolution. The latter unit
is invertible, and cancels with its inverse in the definition of the single-complex
comparison. Apply homologyFunctorObjQIso naturality to the remaining resolution map.
The embedding from natural-number complexes to integer complexes preserves degree-zero
homology. Under this identification the remaining map is the lift of G applied to the
resolution augmentation into degree-zero cycles, followed by isoHomologyπ₀. This is
exactly InjectiveResolution.toRightDerivedZero', and composing isoRightDerivedObj.inv
gives G.toRightDerivedZero.app Y. -/
theorem rightDerivedPlusSingleUnitHomology_comp_comparison (Y : B) :
    G.rightDerivedPlusSingleUnitHomology Y ≫
      (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app Y =
    G.toRightDerivedZero.app Y := by
  -- Cancel the unit on the resolution using naturality along its augmentation.
  let R := injectiveResolution Y
  let S : CochainComplex.Plus B :=
    ⟨(CochainComplex.singleFunctor B 0).obj Y, 0, inferInstance⟩
  let L : CochainComplex.Plus B := ⟨R.cochainComplex, 0, inferInstance⟩
  let g : S ⟶ L := ObjectProperty.homMk R.ι'
  have htransport :
      (DerivedCategory.Plus.ι.preimageIso
        (X := (DerivedCategory.Plus.singleFunctor B 0).obj Y)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor B 0).obj Y))
        ((DerivedCategory.singleFunctorIsoCompQ B 0).app Y ≪≫
          (DerivedCategory.quotientCompQhIso B).symm.app _)).inv ≫
      (DerivedCategory.Plus.ι.preimageIso
        (X := (DerivedCategory.Plus.singleFunctor B 0).obj Y)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient B).obj L))
        ((DerivedCategory.singleFunctorIsoCompQ B 0).app Y ≪≫
          asIso (DerivedCategory.Q.map R.ι') ≪≫
          (DerivedCategory.quotientCompQhIso B).symm.app _)).hom =
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient B).map g) := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.map_comp, Functor.preimageIso_inv, Functor.preimageIso_hom,
      Functor.map_preimage, Iso.trans_inv, Iso.trans_hom, Category.assoc,
      Iso.inv_hom_id_assoc, asIso_hom]
    change (DerivedCategory.quotientCompQhIso B).hom.app _ ≫
      DerivedCategory.Q.map R.ι' ≫ (DerivedCategory.quotientCompQhIso B).inv.app _ = _
    erw [(DerivedCategory.quotientCompQhIso B).inv.naturality]
    simp
    rfl
  have hunit := G.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient B).map g)
  have hcancel : G.rightDerivedPlusSingleUnit Y ≫
      (G.rightDerivedFunctorPlusObjSingleFunctorIsoQ Y).hom =
      (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 Y).inv ≫
        DerivedCategory.Plus.Qh.map
          (G.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient B).map g)) := by
    dsimp [rightDerivedPlusSingleUnit, rightDerivedFunctorPlusObjSingleFunctorIsoQ]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc, htransport]
    dsimp only [Functor.comp_map] at hunit
    erw [← Category.assoc _ _ (CategoryTheory.inv _), ← hunit]
    change _ ≫ _ ≫ CategoryTheory.inv
      (G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient B).obj L)) = _
    erw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  simp only [rightDerivedPlusSingleUnitHomology,
    singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso,
    NatIso.ofComponents_hom_app, homologyRightDerivedFunctorPlusObjSingleFunctorIso,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  erw [← Functor.map_comp_assoc, hcancel]
  -- The remaining derived morphism is the image of the mapped augmentation.
  let a := (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app Y ≫
    (G.mapHomologicalComplex (.up ℤ)).map R.ι'
  let SC : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj (G.obj Y), 0, inferInstance⟩
  let a' : SC ⟶ G.rightDerivedPlusComplex Y := ObjectProperty.homMk a
  have hmap : (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 Y).inv ≫
      DerivedCategory.Plus.Qh.map
        (G.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient B).map g)) =
      DerivedCategory.Plus.Q.map a' := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.map_comp, mapHomotopyCategoryPlusSingleFunctorQhObjIso,
      Functor.preimageIso_inv, Functor.map_preimage, Functor.mapIso_inv]
    change DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app Y) ≫
      DerivedCategory.Qh.map
        (G.mapHomotopyCategory (.up ℤ) |>.map
          ((HomotopyCategory.quotient B (.up ℤ)).map R.ι')) = _
    rw [Functor.mapHomotopyCategory_map]
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ = DerivedCategory.Q.map a
    exact (DerivedCategory.Q.map_comp _ _).symm
  erw [hmap]
  erw [DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality_assoc]
  -- Remove the single-complex and quotient homology comparisons.
  have hsingle :
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app (G.obj Y) ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso SC 0).hom =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (G.obj Y)).inv := by
    simp only [id_obj, comp_obj, DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso,
      DerivedCategory.singleFunctorCompHomologyFunctorIso,
      HomologicalComplex.homologyFunctorSingleIso, Iso.trans_inv,
      isoWhiskerLeft_inv, Category.assoc, isoWhiskerRight_inv, mapIso_inv,
      SingleFunctors.evaluation_map, NatTrans.comp_app, NatIso.ofComponents_inv_app,
      whiskerLeft_app, associator_inv_app, whiskerRight_app, Category.id_comp,
      DerivedCategory.Plus.homologyFunctorObjQIso, ObjectProperty.ι_obj,
      Iso.trans_hom, Iso.app_hom, SC]
    rw [DerivedCategory.singleFunctorsPostcompQIso_inv_hom]
    change _ ≫ _ ≫ (DerivedCategory.homologyFunctor C 0).map (𝟙 _) ≫
      (DerivedCategory.homologyFunctorFactorsh C 0).hom.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj SC.obj) ≫ _ = _
    rw [Functor.map_id, Category.id_comp,
      DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj]
    have hq : (DerivedCategory.quotientCompQhIso C).hom.app SC.obj = 𝟙 _ := rfl
    rw [hq, Functor.map_id, Category.id_comp]
    simp only [Category.assoc]
    change _ ≫ (DerivedCategory.homologyFunctorFactors C 0).inv.app SC.obj ≫
      (DerivedCategory.homologyFunctorFactors C 0).hom.app SC.obj ≫
      (HomotopyCategory.homologyFunctorFactors C (.up ℤ) 0).inv.app SC.obj ≫
      (HomotopyCategory.homologyFunctorFactors C (.up ℤ) 0).hom.app SC.obj = _
    simp
  erw [← Category.assoc, hsingle]
  rw [R.toRightDerivedZero_eq G]
  simp only [InjectiveResolution.isoRightDerivedObjCochainComplex,
    Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    HomologicalComplex.homologyFunctor_map, Category.assoc]
  simp only [← Category.assoc]
  apply (cancel_mono (R.isoRightDerivedObj G 0).inv).2
  let K := (G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  let b := a ≫ (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat G).hom
  -- Identify the degree-zero cycles lift by composing with the cycles inclusion.
  have hc :
      (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 (G.obj Y)).inv ≫
        HomologicalComplex.cyclesMap b 0 ≫
        (K.extendCyclesIso ComplexShape.embeddingUpNat (by simp : (0 : ℕ) = (0 : ℤ))).hom =
      R.toRightDerivedZero' G := by
    apply (cancel_mono (K.iCycles 0)).1
    simp only [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles]
    erw [HomologicalComplex.cyclesMap_i_assoc,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    erw [HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc]
    dsimp [b, a]
    simp only [Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Category.assoc]
    rw [InjectiveResolution.ι'_f_zero]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    simp only [Iso.inv_hom_id_assoc]
    dsimp [InjectiveResolution.cochainComplexXIso, HomologicalComplex.mapExtendIso,
      HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso]
    dsimp only [HomologicalComplex.Hom.isoOfComponents]
    erw [HomologicalComplex.mapExtendX_hom_eq R.cocomplex G
      (ComplexShape.embeddingUpNat.r_f 0)]
    simp [eqToHom_map]
  simp only [Category.assoc]
  erw [← HomologicalComplex.homologyMap_comp_assoc]
  change (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (G.obj Y)).inv ≫
    HomologicalComplex.homologyMap b 0 ≫
      (K.extendHomologyIso ComplexShape.embeddingUpNat (by simp : (0 : ℕ) = (0 : ℤ))).hom = _
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ,
    Category.assoc, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom]
  change _ = R.toRightDerivedZero' G ≫ K.homologyπ 0
  exact (by simpa only [Category.assoc] using
    congrArg (fun f => f ≫ K.homologyπ 0) hc)

end CategoryTheory.Functor
