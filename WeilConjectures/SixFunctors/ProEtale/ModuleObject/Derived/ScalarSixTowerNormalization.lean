/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.CategoryTheory.HomotopyConjugateComposition
import WeilConjectures.CategoryTheory.DerivedConjugateNormalization
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
/-! # The scalar tower on homotopy representatives -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor DerivedCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing
/-- Degreewise induction preserves the composite restriction comparison. -/
private theorem homotopy_composite
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (S : A ⥤ B) (R : B ⥤ C) (U V : A ⥤ C)
    [S.Additive] [R.Additive] [U.Additive] [V.Additive]
    (e₁ : U ≅ V) (e₂ : V ≅ S ⋙ R) (N : HomotopyCategory A (.up ℤ)) :
    ((NatTrans.mapHomotopyCategory e₁.hom (.up ℤ)).app N ≫
        (NatTrans.mapHomotopyCategory e₂.hom (.up ℤ)).app N) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (S ⋙ R)) (.up ℤ)).inv.app N =
    (Functor.mapHomotopyCategoryCompIso (e₁ ≪≫ e₂).symm (.up ℤ)).inv.app N := by
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective N
  change ((HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _) ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ =
    (HomotopyCategory.quotient C (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.symm_inv, Iso.trans_hom,
    NatTrans.comp_app, Iso.refl_inv, NatTrans.id_app,
    HomotopyCategory.quotient_obj_as]
  exact Category.comp_id _
/-- The ordinary extension-of-scalars tower, fixed by restriction transitivity.
Source: uniqueness of adjoints (blueprint: lem-sf-scalar-tower-normalization).
Its construction is the ordinary analogue of `scalarSixTower`. -/
def scalarSixOrdinaryTower {Λ₀ Λ₁ Λ₂ : ScalarSixRing.{u}}
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (X : Scheme.{u}) :=
  (conjugateIsoEquiv
    (Mod.extendRestrictAdjunction (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₂.X) (a ≫ b).hom.hom X))
    ((Mod.extendRestrictAdjunction (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)).comp
      (Mod.extendRestrictAdjunction (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)))).symm
    (Mod.comapCongr (coefficientMap_comp (Λ := Λ₀.X) (Λ' := Λ₁.X) (Λ'' := Λ₂.X)
      a.hom.hom b.hom.hom X) ≪≫
      Mod.comapComp _ _)
/-- The ordinary tower applied degreewise and then passed to homotopy classes.
Source: degreewise extension of scalars (blueprint: lem-sf-scalar-tower-normalization). -/
def scalarSixHomotopyTower {Λ₀ Λ₁ Λ₂ : ScalarSixRing.{u}}
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (X : Scheme.{u}) :=
  Functor.mapHomotopyCategoryCompIso (scalarSixOrdinaryTower a b X) (.up ℤ)
set_option maxHeartbeats 4000000 in
-- The proof unfolds the canonical adjunctions and their localization comparison maps.
/-- The canonical scalar tower is computed by ordinary scalar transitivity through the
left-derived counits.
Source: unit characterization of conjugates (blueprint: lem-sf-scalar-tower-normalization).
Proof: the individual derived extension adjunctions satisfy the unit computation formula.
Compose those formulas, and use the exact restriction composition formula. The general
conjugate normalization lemma then computes the derived conjugate; the degreewise unit
identity identifies its homotopy counterpart with the ordinary tower. -/
theorem scalarSixTower_counit {Λ₀ Λ₁ Λ₂ : ScalarSixRing.{u}}
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (X : Scheme.{u})
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ₀.X X)) (.up ℤ)) :
    (scalarSixTower a b X).hom.app (Qh.obj P) ≫
        (Mod.extendScalars
          (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₂.X)
            (a ≫ b).hom.hom X)).leftDerivedFunctorCounit.app P =
      (scalarSixChange b X).map
          ((Mod.extendScalars
            (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X)
              a.hom.hom X)).leftDerivedFunctorCounit.app P) ≫
        (Mod.extendScalars
          (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)).leftDerivedFunctorCounit.app
          (((Mod.extendScalars
              (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X)
                a.hom.hom X)).mapHomotopyCategory (.up ℤ)).obj P) ≫
        Qh.map ((scalarSixHomotopyTower a b X).hom.app P) := by
  let F := Mod.extendScalars (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)
  let G := Mod.extendScalars (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)
  let H := Mod.extendScalars (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₂.X) (a ≫ b).hom.hom X)
  let R := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)
  let S := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)
  let T := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₂.X) (a ≫ b).hom.hom X)
  let aa : F ⊣ R :=
    Mod.extendRestrictAdjunction (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)
  let bb : G ⊣ S :=
    Mod.extendRestrictAdjunction (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)
  let hh : H ⊣ T :=
    Mod.extendRestrictAdjunction (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₂.X) (a ≫ b).hom.hom X)
  let ad : F.leftDerivedFunctor ⊣ R.mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)
  let bd : G.leftDerivedFunctor ⊣ S.mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)
  let hd : H.leftDerivedFunctor ⊣ T.mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₂.X) (a ≫ b).hom.hom X)
  let c : Qh ⋙ (F.leftDerivedFunctor ⋙ G.leftDerivedFunctor) ⟶
      (F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ)) ⋙ Qh :=
    whiskerRight F.leftDerivedFunctorCounit G.leftDerivedFunctor ≫
      whiskerLeft (F.mapHomotopyCategory (.up ℤ)) G.leftDerivedFunctorCounit
  let d : (S.mapHomotopyCategory (.up ℤ) ⋙ R.mapHomotopyCategory (.up ℤ)) ⋙ Qh ⟶
      Qh ⋙ (S.mapDerivedCategory ⋙ R.mapDerivedCategory) :=
    whiskerLeft (S.mapHomotopyCategory (.up ℤ)) R.mapDerivedCategoryFactorsh.inv ≫
      whiskerRight S.mapDerivedCategoryFactorsh.inv R.mapDerivedCategory
  let r : T ≅ S ⋙ R := Mod.comapCongr (coefficientMap_comp (Λ := Λ₀.X) (Λ' := Λ₁.X) (Λ'' := Λ₂.X)
      a.hom.hom b.hom.hom X) ≪≫
    Mod.comapComp (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)
      (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)
  let rk := (Functor.mapHomotopyCategoryCompIso r.symm (.up ℤ)).inv
  let rd : T.mapDerivedCategory ⟶ S.mapDerivedCategory ⋙ R.mapDerivedCategory :=
    (Functor.mapDerivedCategoryNatIso
        (Mod.comapCongr (coefficientMap_comp (Λ := Λ₀.X) (Λ' := Λ₁.X) (Λ'' := Λ₂.X)
      a.hom.hom b.hom.hom X)) ≪≫
      Functor.mapDerivedCategoryNatIso (Mod.comapComp _ _) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom
  have hcomp := unit_normalization_comp Qh Qh Qh
    (aa.mapHomotopyCategory (.up ℤ)) (bb.mapHomotopyCategory (.up ℤ)) ad bd
    F.leftDerivedFunctorCounit G.leftDerivedFunctorCounit
    R.mapDerivedCategoryFactorsh.inv S.mapDerivedCategoryFactorsh.inv
    (Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh _)
    (Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh _)
  have hr (N) : T.mapDerivedCategoryFactorsh.inv.app N ≫ rd.app (Qh.obj N) =
      Qh.map (rk.app N) ≫ d.app N := by
    dsimp only [rd, d, Iso.trans_hom, NatTrans.comp_app,
      whiskerLeft_app, whiskerRight_app]
    erw [Functor.mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app_assoc,
      Functor.mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app_assoc,
      Functor.mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryCompIso_hom_app]
    erw [← Qh.map_comp_assoc, ← Qh.map_comp_assoc, homotopy_composite]
  have hn := conjugate_normalization Qh Qh
    (hh.mapHomotopyCategory (.up ℤ))
    ((aa.mapHomotopyCategory (.up ℤ)).comp (bb.mapHomotopyCategory (.up ℤ)))
    hd (ad.comp bd) H.leftDerivedFunctorCounit c T.mapDerivedCategoryFactorsh.inv d
    (Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh _) hcomp rk rd hr P
  erw [homotopyConjugateComp aa bb hh r P] at hn
  have hleft : (scalarSixTower a b X).hom =
      (conjugateEquiv hd (ad.comp bd)).symm rd := by
    rfl
  have hright : scalarSixHomotopyTower a b X =
      Functor.mapHomotopyCategoryCompIso
        ((conjugateIsoEquiv hh (aa.comp bb)).symm r) (.up ℤ) := by
    rfl
  erw [hleft, hright]
  simpa only [F, G, H, scalarSixChange, scalarSixAdjunctionLeft, c,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Category.assoc] using hn
end AlgebraicGeometry.ProEtale.CondensedRing
