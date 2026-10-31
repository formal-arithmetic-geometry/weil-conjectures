/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.LocalRHomPresheafModel
public import WeilConjectures.Algebra.Homology.LocalRHomCocycleComparison
import WeilConjectures.Algebra.Homology.LocalRHomCanonicalNaturality
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Local RHom comparison and its cohomological lower bound

Source: Stacks Project, Tags 0A94, 0A95 and 0149.
(blueprint: lem-per-local-rhom-section-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe uC vC u w wSlice
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules
namespace CategoryTheory.LocalRHom.Sections

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max uC vC u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  (R : Sheaf J CommRingCat.{max uC vC u})
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))]


/-- Transporting derived arrows along isomorphisms is additive.
Source: Stacks Project, Tag 05RR.
(blueprint: lem-per-local-rhom-section-equivalence). -/
def homAddEquiv {E : Type*} [Category E] [Preadditive E] {X Y X' Y' : E}
    (s : X ≅ X') (t : Y ≅ Y') : (X ⟶ Y) ≃+ (X' ⟶ Y') :=
  { Iso.homCongr s t with
    map_add' := fun f g ↦ by
      dsimp [Iso.homCongr]
      simp only [Preadditive.comp_add, Preadditive.add_comp] }

/-- The comparison between the two orders of restriction and shifting.
Source: Stacks Project, Tag 015F.
(blueprint: lem-per-local-rhom-section-equivalence). -/
def shiftedRestrictionIso
    (I : CochainComplex (Mod.{uC, vC, u} J R) ℤ) (n : ℤ) (U : C) :
    DerivedCategory.Q.obj (((complexRes.{uC, vC, u} J R U).obj I)⟦n⟧) ≅
      (res.{uC, vC, u, w, wSlice} J R U).obj ((DerivedCategory.Q.obj I)⟦n⟧) :=
  DerivedCategory.Q.mapIso (((complexRes.{uC, vC, u} J R U).commShiftIso n).symm.app I) ≪≫
    (resQ.{uC, vC, u, w, wSlice} J R U (I⟦n⟧)).symm ≪≫
    (res.{uC, vC, u, w, wSlice} J R U).mapIso
      ((DerivedCategory.Q.commShiftIso n).app I)

/-- Naturality of the termwise-to-derived restriction factorization.
Source: Stacks Project, Tag 015F.
(blueprint: lem-per-local-rhom-section-equivalence). -/
theorem resQ_naturality
    {X Y : CochainComplex (Mod.{uC, vC, u} J R) ℤ} (f : X ⟶ Y) (U : C) :
    (res.{uC, vC, u, w, wSlice} J R U).map (DerivedCategory.Q.map f) ≫
        (resQ.{uC, vC, u, w, wSlice} J R U Y).hom =
      (resQ.{uC, vC, u, w, wSlice} J R U X).hom ≫
        DerivedCategory.Q.map ((complexRes.{uC, vC, u} J R U).map f) := by
  have := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u}
    (rings.{uC, vC, u} J R) U).1
  have := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u}
    (rings.{uC, vC, u} J R) U).2
  exact (SheafOfModules.overFunctor.{max uC vC u}
    (rings.{uC, vC, u} J R) U).mapDerivedCategoryFactors.hom.naturality f

/-- Naturality of the comparison between the two orders of restriction and shifting.
Source: Stacks Project, Tag 015F.
(blueprint: lem-per-local-rhom-section-equivalence). -/
theorem shiftedRestrictionIso_naturality
    {X Y : CochainComplex (Mod.{uC, vC, u} J R) ℤ} (f : X ⟶ Y) (n : ℤ) (U : C) :
    DerivedCategory.Q.map (((complexRes.{uC, vC, u} J R U).map f)⟦n⟧') ≫
        (shiftedRestrictionIso.{uC, vC, u, w, wSlice} J R Y n U).hom =
      (shiftedRestrictionIso.{uC, vC, u, w, wSlice} J R X n U).hom ≫
        (res.{uC, vC, u, w, wSlice} J R U).map ((DerivedCategory.Q.map f)⟦n⟧') := by
  have h₁ := ((complexRes.{uC, vC, u} J R U).commShiftIso n).inv.naturality f
  have h₂ := resQ_naturality.{uC, vC, u, w, wSlice} J R (f⟦n⟧') U
  have h₃ := (DerivedCategory.Q.commShiftIso n).hom.naturality f
  dsimp only [Functor.comp_map] at h₁ h₃
  dsimp [shiftedRestrictionIso]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  rw [h₁, Functor.map_comp]
  simp only [Category.assoc]
  have h₂' : DerivedCategory.Q.map ((complexRes.{uC, vC, u} J R U).map (f⟦n⟧')) ≫
      (resQ.{uC, vC, u, w, wSlice} J R U (Y⟦n⟧)).inv =
        (resQ.{uC, vC, u, w, wSlice} J R U (X⟦n⟧)).inv ≫
          (res.{uC, vC, u, w, wSlice} J R U).map (DerivedCategory.Q.map (f⟦n⟧')) := by
    apply (Iso.eq_inv_comp
      (resQ.{uC, vC, u, w, wSlice} J R U (X⟦n⟧))).2
    rw [← Category.assoc, ← h₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% h₂']
  simp only [← Functor.map_comp, h₃]

/-- Evaluation identifies the localized presheaf with the resolved Hom complex on sections.
Source: Stacks Project, Tags 0A94 and 0A95.
(blueprint: lem-per-local-rhom-section-equivalence). -/
def presheafSectionsEquiv
    (L X : CochainComplex (Mod.{uC, vC, u} J R) ℤ) (n : ℤ) (U : C) :
    ((Model.presheaf.{uC, vC, u, w} J R L n).obj
      (DerivedCategory.Q.obj X)).obj (op U) ≃+
        (Cocycle.sectionComplex.{uC, vC, u} J R L
          ((WeilConjectures.coefficientHomResolution.{u, uC, vC} J R).obj X) U).homology n := by
  let ev := PresheafOfModules.evaluation (rings.{uC, vC, u} J R).obj (op U) ⋙
    forget₂ (ModuleCat.{max uC vC u} ((rings.{uC, vC, u} J R).obj.obj (op U))) AddCommGrpCat
  exact (ev.mapIso ((Model.presheafFactors.{uC, vC, u, w}
    J R L n).app X)).addCommGroupIsoToAddEquiv.trans
      (Model.evaluationHomologyIso.{uC, vC, u} J R
        ((Model.homPresheaf.{uC, vC, u} J R L).obj X) n U).symm.addCommGroupIsoToAddEquiv

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))] in
/-- Naturality of the evaluation and cohomology factorization before local comparison.
Source: Stacks Project, Tags 03EI and 0A95.
(blueprint: lem-per-local-rhom-section-equivalence). -/
theorem presheafSectionsEquiv_naturality
    (L X Y : CochainComplex (Mod.{uC, vC, u} J R) ℤ) (f : X ⟶ Y)
    (n : ℤ) (U : C)
    (x : ((Model.presheaf.{uC, vC, u, w} J R L n).obj
      (DerivedCategory.Q.obj X)).obj (op U)) :
    presheafSectionsEquiv.{uC, vC, u, w} J R L Y n U
        (((Model.presheaf.{uC, vC, u, w} J R L n).map
          (DerivedCategory.Q.map f)).app (op U) x) =
      HomologicalComplex.homologyMap
        (((PresheafOfModules.evaluation (rings.{uC, vC, u} J R).obj (op U) ⋙
          forget₂ (ModuleCat.{max uC vC u} ((rings.{uC, vC, u} J R).obj.obj (op U)))
            AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
              ((Model.homPresheaf.{uC, vC, u} J R L).map f)) n
        (presheafSectionsEquiv.{uC, vC, u, w} J R L X n U x) := by
  let ev := PresheafOfModules.evaluation (rings.{uC, vC, u} J R).obj (op U) ⋙
    forget₂ (ModuleCat.{max uC vC u} ((rings.{uC, vC, u} J R).obj.obj (op U))) AddCommGrpCat
  let α := Functor.isoWhiskerRight (Model.presheafFactors.{uC, vC, u, w} J R L n) ev
  let β := Functor.isoWhiskerLeft
    (Model.homPresheaf.{uC, vC, u} J R L ⋙
      HomologicalComplex.shortComplexFunctor _ (.up ℤ) n)
    (ShortComplex.homologyFunctorIso ev).symm
  exact ConcreteCategory.congr_hom ((α ≪≫ β).hom.naturality f) x

/-- The section equivalence on an arbitrary complex representative of the target.
Source: Stacks Project, Tags 0A94 and 0A95.
(blueprint: lem-per-local-rhom-section-equivalence). -/
def sectionEquivOnQ
    (L X : CochainComplex (Mod.{uC, vC, u} J R) ℤ) (n : ℤ) (U : C) :
    ((Model.presheaf.{uC, vC, u, w} J R L n).obj
      (DerivedCategory.Q.obj X)).obj (op U) ≃+
        ((res.{uC, vC, u, w, wSlice} J R U).obj (DerivedCategory.Q.obj L) ⟶
          (res.{uC, vC, u, w, wSlice} J R U).obj ((DerivedCategory.Q.obj X)⟦n⟧)) := by
  let A := Mod.{uC, vC, u} J R
  let : IsGrothendieckAbelian.{max uC vC u} A :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{uC, vC, u} J R).1
  let I := (WeilConjectures.coefficientHomResolution.{u, uC, vC} J R).obj X
  have : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max uC vC u} A X
  let η := (CochainComplex.toKInjectiveResolution.{max uC vC u} A).app X
  have : QuasiIso η := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app A X).2
  let k : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj X :=
    (asIso (DerivedCategory.Q.map η)).symm
  let a := Cocycle.cohomologyEquiv.{uC, vC, u, wSlice} J R L I U n
  exact (presheafSectionsEquiv.{uC, vC, u, w} J R L X n U).trans
    (a.trans (homAddEquiv (resQ.{uC, vC, u, w, wSlice} J R U L).symm
      (shiftedRestrictionIso.{uC, vC, u, w, wSlice} J R I n U ≪≫
        (res.{uC, vC, u, w, wSlice} J R U).mapIso ((shiftFunctor _ n).mapIso k))))

/-- The concrete comparison on complex representatives is natural in chain maps.
Source: Stacks Project, Tags 0A8Y, 0A94 and 0A95.
(blueprint: lem-per-local-rhom-section-equivalence). -/
theorem sectionEquivOnQ_naturality
    (L X Y : CochainComplex (Mod.{uC, vC, u} J R) ℤ) (f : X ⟶ Y)
    (n : ℤ) (U : C)
    (x : ((Model.presheaf.{uC, vC, u, w} J R L n).obj
      (DerivedCategory.Q.obj X)).obj (op U)) :
    sectionEquivOnQ.{uC, vC, u, w, wSlice} J R L Y n U
        (((Model.presheaf.{uC, vC, u, w} J R L n).map
          (DerivedCategory.Q.map f)).app (op U) x) =
      sectionEquivOnQ.{uC, vC, u, w, wSlice} J R L X n U x ≫
        (res.{uC, vC, u, w, wSlice} J R U).map ((DerivedCategory.Q.map f)⟦n⟧') := by
  have :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{uC, vC, u} J R).1
  let I := WeilConjectures.coefficientHomResolution.{u, uC, vC} J R
  have : (I.obj X).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max uC vC u} _ X
  have : (I.obj Y).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max uC vC u} _ Y
  have h := localRHom_canonical_naturality.{uC, vC, u, wSlice}
    R U (I.map f) (𝟙 L) n (presheafSectionsEquiv.{uC, vC, u, w} J R L X n U x)
  simp only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  have hp := presheafSectionsEquiv_naturality.{uC, vC, u, w} J R L X Y f n U x
  have hs := shiftedRestrictionIso_naturality.{uC, vC, u, w, wSlice} J R (I.map f) n U
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{max uC vC u}
      (Mod.{uC, vC, u} J R)).app X) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ X).2
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{max uC vC u}
      (Mod.{uC, vC, u} J R)).app Y) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ Y).2
  have hη := (CochainComplex.toKInjectiveResolution.{max uC vC u}
    (Mod.{uC, vC, u} J R)).naturality f
  dsimp only [sectionEquivOnQ, AddEquiv.trans_apply, homAddEquiv, Iso.homCongr]
  rw [hp]
  simp only [AddEquiv.coe_mk, Equiv.coe_fn_mk]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change (resQ.{uC, vC, u, w, wSlice} J R U L).hom ≫
    Cocycle.cohomologyEquiv.{uC, vC, u, wSlice} J R L (I.obj Y) U n _ ≫
      (shiftedRestrictionIso.{uC, vC, u, w, wSlice} J R (I.obj Y) n U).hom ≫ _ =
    ((resQ.{uC, vC, u, w, wSlice} J R U L).hom ≫
      Cocycle.cohomologyEquiv.{uC, vC, u, wSlice} J R L (I.obj X) U n _ ≫
        (shiftedRestrictionIso.{uC, vC, u, w, wSlice} J R (I.obj X) n U).hom ≫ _) ≫ _
  erw [h]
  simp only [Category.assoc]
  rw [reassoc_of% hs]
  simp only [← Functor.map_comp]
  congr 3
  apply (res.{uC, vC, u, w, wSlice} J R U).congr_map
  apply (shiftFunctor _ n).congr_map
  have hη' := congrArg DerivedCategory.Q.map hη
  simp only [Functor.map_comp] at hη'
  rw [← cancel_epi (DerivedCategory.Q.map
    ((CochainComplex.toKInjectiveResolution.{max uC vC u}
      (Mod.{uC, vC, u} J R)).app X))]
  simp only [← Category.assoc]
  erw [← hη']
  simp only [Functor.id_map, asIso_inv, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]
  simp

/-- Sectionwise local derived morphisms for every target object.
Source: Stacks Project, Tags 0A94 and 0A95.
(blueprint: lem-per-local-rhom-section-equivalence). -/
def sectionEquiv
    (K : D.{uC, vC, u, w} J R) (L : CochainComplex (Mod.{uC, vC, u} J R) ℤ)
    (k : DerivedCategory.Q.obj L ≅ K) (n : ℤ) (M : D.{uC, vC, u, w} J R) (U : C) :
    ((Model.presheaf.{uC, vC, u, w} J R L n).obj M).obj (op U) ≃+
      ((res.{uC, vC, u, w, wSlice} J R U).obj K ⟶
        (res.{uC, vC, u, w, wSlice} J R U).obj (M⟦n⟧)) := by
  let Q : CochainComplex (Mod.{uC, vC, u} J R) ℤ ⥤ D.{uC, vC, u, w} J R :=
    DerivedCategory.Q
  let X := Q.objPreimage M
  let i : Q.obj X ≅ M := Q.objObjPreimageIso M
  let ev := PresheafOfModules.evaluation (rings.{uC, vC, u} J R).obj (op U) ⋙
    forget₂ (ModuleCat.{max uC vC u} ((rings.{uC, vC, u} J R).obj.obj (op U))) AddCommGrpCat
  let a := (ev.mapIso ((Model.presheaf.{uC, vC, u, w} J R L n).mapIso i.symm))
  exact a.addCommGroupIsoToAddEquiv.trans
      ((sectionEquivOnQ.{uC, vC, u, w, wSlice} J R L X n U).trans
        (homAddEquiv ((res.{uC, vC, u, w, wSlice} J R U).mapIso k)
          ((res.{uC, vC, u, w, wSlice} J R U).mapIso ((shiftFunctor _ n).mapIso i))))

end CategoryTheory.LocalRHom.Sections
