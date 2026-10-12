/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapScalarCompatibility
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapDataTargetNaturality

/-! # Basic properties of maps on module cohomology

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Tags 01F8--01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-properties).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def resolutionComparison {Z : Scheme.{u}}
    {F : SheafOfModules.{u} Z.ringCatSheaf} (I : InjectiveResolution F) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj ((Z.toRingedSpace.moduleCohomology p).obj F) ≅
      (((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex).homology p :=
  (forget₂ _ AddCommGrpCat.{u}).mapIso
    (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Z.toRingedSpace) p) ≪≫
    (((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).symm

private theorem resolutionComparison_naturality {Z : Scheme.{u}}
    {G F : SheafOfModules.{u} Z.ringCatSheaf} (ψ : G ⟶ F)
    (J : InjectiveResolution G) (I : InjectiveResolution F)
    (f : J.cocomplex ⟶ I.cocomplex)
    (hf : J.ι.f 0 ≫ f.f 0 = ψ ≫ I.ι.f 0) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).map
        ((Z.toRingedSpace.moduleCohomology p).map ψ) ≫ (resolutionComparison I p).hom =
      (resolutionComparison J p).hom ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
          (((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
            forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
              f) := by
  set_option backward.isDefEq.respectTransparency false in
    let : EnoughInjectives (SheafOfModules.{u} Z.ringCatSheaf) :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives Z.toRingedSpace).2
    dsimp only [RingedSpace.moduleCohomology, resolutionComparison, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, ← Functor.map_comp,
      J.isoRightDerivedObj_hom_naturality ψ I f hf, Functor.map_comp, Category.assoc]
    simp only [Category.assoc]
    apply congrArg (fun k ↦ (forget₂ _ AddCommGrpCat.{u}).map
      (J.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Z.toRingedSpace) p).hom ≫ k)
    exact ShortComplex.mapHomologyIso_inv_naturality
      (((RingedSpace.globalSectionsFunctor Z.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).map f |> (HomologicalComplex.shortComplexFunctor _ _ p).map)
      (forget₂ _ AddCommGrpCat.{u})

set_option maxHeartbeats 600000 in
-- Resolution comparison unfolds several functors and homology comparison isomorphisms.
private theorem fmapData_id {Z : Scheme.{u}}
    {G F : SheafOfModules.{u} Z.ringCatSheaf}
    (ψ : G ⟶ F) (D : ModuleCohomologyFMapData (𝟙 Z) G F ψ) (p : ℕ) :
    D.map p = (forget₂ _ AddCommGrpCat).map
      ((Z.toRingedSpace.moduleCohomology p).map ψ) := by
  set_option backward.isDefEq.respectTransparency false in
    let : EnoughInjectives (SheafOfModules.{u} Z.ringCatSheaf) :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives Z.toRingedSpace).2
    let e : D.I.cocomplex ≅
        ((pushforward (𝟙 Z)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.I.cocomplex :=
      ((Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} Z.ringCatSheaf)
        (ComplexShape.up ℕ)).app
        D.I.cocomplex).symm ≪≫
        (NatIso.mapHomologicalComplex (pushforwardId Z).symm (ComplexShape.up ℕ)).app
          D.I.cocomplex
    let t := e.hom ≫ D.lambda
    let : QuasiIso D.lambda := D.quasiIso
    let R : InjectiveResolution F :=
      { cocomplex := D.K
        injective := D.injective
        ι := D.I.ι ≫ t }
    have hc : D.J.ι.f 0 ≫ D.β.f 0 = ψ ≫ R.ι.f 0 := by
      rw [D.compatible]
      dsimp [R, t, e]
      have hi : (pushforward (𝟙 Z)).map (D.I.ι.f 0) =
          D.I.ι.f 0 ≫ (pushforwardId Z).inv.app (D.I.cocomplex.X 0) := by
        ext U x
        rfl
      simp [hi]
    have hnat := resolutionComparison_naturality ψ D.J R D.β hc p
    have ht := resolutionComparison_naturality (𝟙 F) D.I R t (by simp [R]) p
    have ha : D.a.hom =
        ((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map e.hom := by
      let S := (RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
      have hi : D.a.inv = S.map e.inv := by
        apply HomologicalComplex.Hom.ext
        funext n
        rw [D.sections]
        change (presheaf (D.I.cocomplex.X n)).map (𝟙 _) = 𝟙 _
        exact CategoryTheory.Functor.map_id _ _
      apply (cancel_epi D.a.inv).1
      rw [D.a.inv_hom_id, hi, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
    let S := (RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
    have hmu : D.a.hom ≫ S.map D.lambda = S.map t := by
      rw [ha, ← Functor.map_comp]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at ht
    let : IsIso (H.map (D.a.hom ≫ S.map D.lambda)) := D.invertible p
    let : IsIso (H.map (S.map t)) := by
      rw [← hmu]
      exact D.invertible p
    change (resolutionComparison D.J p).hom ≫ H.map (S.map D.β) ≫
      inv (H.map (D.a.hom ≫ S.map D.lambda)) ≫ (resolutionComparison D.I p).inv = _
    simp only [hmu]
    rw [← reassoc_of% hnat, ht]
    simp only [Category.assoc]
    erw [IsIso.hom_inv_id_assoc (H.map (S.map t))]
    rw [Iso.hom_inv_id, Category.comp_id]

/-- Linearity, degree zero, identity, and restriction properties of the map induced by an
`h`-map.  The degree-zero clause is expressed using the canonical derived-functor
identifications with global sections.
Source: Stacks Project, Cohomology of Sheaves, Section 01F7;
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-properties).

Proof: scalar compatibility of the resolution formula bundles the linear map.
The augmentation square and the canonical degree-zero derived-functor isomorphisms
give the degree-zero clause. For the identity scheme map, K itself is an injective
resolution of F; two applications of resolution-comparison naturality cancel the
vertical homology isomorphism. For restriction, uniqueness of left adjoints supplies
κ and its unit equation, and target naturality of the resolution formula gives the
cohomology equation. The scalar, augmentation, and target-naturality statements
remain the three separately named obligations imported above.
-/
theorem moduleCohomologyFMap_basic_properties {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    (∃ L : (Y.toRingedSpace.moduleCohomology p).obj G ⟶
          (ModuleCat.restrictScalars h.appTop.hom).obj
            ((X.toRingedSpace.moduleCohomology p).obj F),
      (forget₂ _ AddCommGrpCat).map L = moduleCohomologyFMap h φ p) ∧
    (∃ eG : (Y.toRingedSpace.moduleCohomology 0).obj G ≅
          (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj G,
      ∃ eF : (X.toRingedSpace.moduleCohomology 0).obj F ≅
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj F,
        (forget₂ _ AddCommGrpCat).map eG.hom ≫
            (forget₂ _ AddCommGrpCat).map
              ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) =
          moduleCohomologyFMap h φ 0 ≫
            (forget₂ _ AddCommGrpCat).map eF.hom) ∧
    (∀ (Z : Scheme.{u}) (GZ FZ : SheafOfModules.{u} Z.ringCatSheaf)
      (ψ : GZ ⟶ FZ),
      moduleCohomologyFMap (𝟙 Z) ψ p =
        (forget₂ _ AddCommGrpCat).map
          ((Z.toRingedSpace.moduleCohomology p).map ψ)) ∧
    (∀ (U : Y.Opens),
      ∃ κ : (restrictFunctor U.ι).obj G ≅ (tensorPullback U.ι).obj G,
        moduleCohomologyFMap U.ι ((restrictAdjunction U.ι).unit.app G) p ≫
            (forget₂ _ AddCommGrpCat).map
              (((U : Scheme).toRingedSpace.moduleCohomology p).map κ.hom) =
          moduleCohomologyFMap U.ι
            ((Classical.choose (exists_tensorPullbackAdjunction U.ι)).unit.app G) p)
 := by
  set_option backward.isDefEq.respectTransparency false in
    let D := Classical.choice (moduleCohomologyFMapData_nonempty h G F φ)
    refine ⟨?_, ?_, ?_, ?_⟩
    · let L : (Y.toRingedSpace.moduleCohomology p).obj G ⟶
          (ModuleCat.restrictScalars h.appTop.hom).obj
            ((X.toRingedSpace.moduleCohomology p).obj F) :=
        ModuleCat.ofHom (Y := (ModuleCat.restrictScalars h.appTop.hom).obj
          ((X.toRingedSpace.moduleCohomology p).obj F))
          { toFun := fun x ↦ (D.map p).hom x
            map_add' := fun x y ↦ (D.map p).hom.map_add x y
            map_smul' := fun r x ↦ D.map_smul p r x }
      refine ⟨L, ?_⟩
      ext x
      rfl
    · let : EnoughInjectives (SheafOfModules.{u} Y.ringCatSheaf) :=
        (RingedSpace.moduleSheaves_abelian_enoughInjectives Y.toRingedSpace).2
      let : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
        (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
      let : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor Y.toRingedSpace) :=
        inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation _ (op ⊤)))
      let : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor X.toRingedSpace) :=
        inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation _ (op ⊤)))
      let eG := (RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedZeroIsoSelf.app G
      let eF := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedZeroIsoSelf.app F
      refine ⟨eG, eF, ?_⟩
      let g := (forget₂ _ AddCommGrpCat.{u}).mapIso eG
      let f := (forget₂ _ AddCommGrpCat.{u}).mapIso eF
      have ha := D.map_zero_augmentation
      change g.inv ≫ D.map 0 =
        (forget₂ _ AddCommGrpCat).map
          ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) ≫ f.inv at ha
      change g.hom ≫ _ = D.map 0 ≫ f.hom
      apply (cancel_mono f.inv).1
      simp only [Category.assoc]
      erw [f.hom_inv_id, Category.comp_id, ← ha, ← Category.assoc, g.hom_inv_id,
        Category.id_comp]
    · intro Z GZ FZ ψ
      exact fmapData_id ψ (Classical.choice
        (moduleCohomologyFMapData_nonempty (𝟙 Z) GZ FZ ψ)) p
    · intro U
      let adj : tensorPullback U.ι ⊣ pushforward U.ι :=
        Classical.choose (exists_tensorPullbackAdjunction U.ι)
      let κ : (restrictFunctor U.ι).obj G ≅ (tensorPullback U.ι).obj G :=
        ((restrictAdjunction U.ι).leftAdjointUniq adj).app G
      refine ⟨κ, ?_⟩
      have hu := (restrictAdjunction U.ι).unit_leftAdjointUniq_hom_app adj G
      let ρ := (restrictAdjunction U.ι).unit.app G
      let D := Classical.choice (moduleCohomologyFMapData_nonempty U.ι G _ ρ)
      let E := Classical.choice (moduleCohomologyFMapData_nonempty U.ι G _
        (ρ ≫ (pushforward U.ι).map κ.hom))
      have hn := ModuleCohomologyFMapData.map_target_naturality U.ι ρ κ.hom D E p
      change moduleCohomologyFMap U.ι ρ p ≫ _ = _
      change moduleCohomologyFMap U.ι ρ p ≫ _ =
        moduleCohomologyFMap U.ι (ρ ≫ (pushforward U.ι).map κ.hom) p at hn
      change ρ ≫ (pushforward U.ι).map κ.hom = adj.unit.app G at hu
      rw [hu] at hn
      exact hn

end AlgebraicGeometry.Scheme.Modules
