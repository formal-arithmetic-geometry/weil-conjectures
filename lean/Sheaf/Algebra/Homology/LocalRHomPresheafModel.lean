/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Algebra.Homology.LocalRHomDefinitions
public import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import Sheaf.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Local RHom comparison and its cohomological lower bound

Source: Stacks Project, Tags 0A94, 0A95 and 0149.
(blueprint: lem-per-local-rhom-presheaf-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe uC vC u w wSlice
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules
namespace CategoryTheory.LocalRHom.Model

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max uC vC u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  (R : Sheaf J CommRingCat.{max uC vC u})
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))]


/-- Concrete interface for the resolved local Hom construction.
Source: Stacks Project, Tags 0A8Y and 0A95.
(blueprint: lem-per-local-rhom-presheaf-model). -/
abbrev A := Mod.{uC, vC, u} J R
/-- Concrete interface for the resolved local Hom construction.
Source: Stacks Project, Tags 0A8Y and 0A95.
(blueprint: lem-per-local-rhom-presheaf-model). -/
abbrev B := PresheafOfModules.{max uC vC u} (rings.{uC, vC, u} J R).obj

/-- Concrete interface for the resolved local Hom construction.
Source: Stacks Project, Tags 0A8Y and 0A95.
(blueprint: lem-per-local-rhom-presheaf-model). -/
def homPresheaf (L : CochainComplex (A.{uC, vC, u} J R) ℤ) :
    CochainComplex (A.{uC, vC, u} J R) ℤ ⥤ CochainComplex (B.{uC, vC, u} J R) ℤ :=
  WeilConjectures.coefficientHomResolution.{u, uC, vC} J R ⋙
    (homComplexFunctor.{uC, vC, max uC vC u, max uC vC u} (R := R)).obj (op L) ⋙
      (SheafOfModules.forget (rings.{uC, vC, u} J R)).mapHomologicalComplex (.up ℤ)

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))] in
theorem presheaf_homology_inverts (L : CochainComplex (A.{uC, vC, u} J R) ℤ) (n : ℤ) :
    (HomologicalComplex.quasiIso (A.{uC, vC, u} J R) (.up ℤ)).IsInvertedBy
      (homPresheaf.{uC, vC, u} J R L ⋙
        HomologicalComplex.homologyFunctor (B.{uC, vC, u} J R) (.up ℤ) n) := by
  intro X Y f hf
  have : QuasiIso f := hf
  have := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{uC, vC, u} J R).1
  let I := CochainComplex.kInjectiveResolutionFunctor.{max uC vC u} (A.{uC, vC, u} J R)
  let η := CochainComplex.toKInjectiveResolution.{max uC vC u} (A.{uC, vC, u} J R)
  have : QuasiIso (I.map f) := by
    have : QuasiIso (η.app X) := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ X).2
    have : QuasiIso (η.app Y) := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ Y).2
    apply (quasiIso_iff_comp_left (η.app X) _).mp
    rw [← η.naturality f]
    change QuasiIso (f ≫ η.app Y)
    infer_instance
  have : (I.obj X).IsKInjective := inferInstance
  have : (I.obj Y).IsKInjective := inferInstance
  let g := ((homComplexFunctor.{uC, vC, max uC vC u, max uC vC u}
    (R := R)).obj (op L)).map (I.map f)
  have hg : ∀ U : C, QuasiIso (((SheafOfModules.forget (rings.{uC, vC, u} J R) ⋙
      PresheafOfModules.evaluation (rings.{uC, vC, u} J R).obj (op U) ⋙
      forget₂ (ModuleCat.{max uC vC u} ((rings.{uC, vC, u} J R).obj.obj (op U)))
        AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map g) := by
    intro U
    simpa [g] using homComplex_sections_quasiIsoOfUniverses.{uC, vC, u} (I.map f) (𝟙 L) U
  let F := homPresheaf.{uC, vC, u} J R L
  let m := (HomologicalComplex.homologyFunctor (B.{uC, vC, u} J R) (.up ℤ) n).map (F.map f)
  suffices hm : ∀ U : Cᵒᵖ, IsIso (m.app U) by
    let e := PresheafOfModules.isoMk (fun U ↦ asIso (m.app U)) (fun {_ _} a ↦ m.naturality a)
    exact e.isIso_hom
  intro U
  let ev := PresheafOfModules.evaluation (rings.{uC, vC, u} J R).obj U ⋙
    forget₂ (ModuleCat.{max uC vC u} ((rings.{uC, vC, u} J R).obj.obj U)) AddCommGrpCat
  have h := hg U.unop
  have : QuasiIso ((ev.mapHomologicalComplex (.up ℤ)).map (F.map f)) := h
  have hi : IsIso (HomologicalComplex.homologyMap
      ((ev.mapHomologicalComplex (.up ℤ)).map (F.map f)) n) := inferInstance
  have hm : IsIso (ev.map m) := by
    exact (NatIso.isIso_map_iff
      (Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor (B.{uC, vC, u} J R) (.up ℤ) n)
        (ShortComplex.homologyFunctorIso ev)) (F.map f)).mp hi
  change IsIso ((forget₂ (ModuleCat.{max uC vC u}
    ((rings.{uC, vC, u} J R).obj.obj U)) AddCommGrpCat).map (m.app U)) at hm
  have := hm
  exact isIso_of_reflects_iso (m.app U)
    (forget₂ (ModuleCat.{max uC vC u} ((rings.{uC, vC, u} J R).obj.obj U)) AddCommGrpCat)

/-- The module presheaf obtained by localizing resolved sectionwise Hom cohomology.
Source: Stacks Project, Tag 0A95.
(blueprint: lem-per-local-rhom-presheaf-model). -/
def presheaf (L : CochainComplex (A.{uC, vC, u} J R) ℤ) (n : ℤ) :
    D.{uC, vC, u, w} J R ⥤ B.{uC, vC, u} J R :=
  Localization.lift
    (homPresheaf.{uC, vC, u} J R L ⋙
      HomologicalComplex.homologyFunctor (B.{uC, vC, u} J R) (.up ℤ) n)
    (presheaf_homology_inverts.{uC, vC, u} J R L n)
    DerivedCategory.Q

/-- The fixed localization factorization for the local Hom presheaf.
Source: Stacks Project, Tag 0A95.
(blueprint: lem-per-local-rhom-presheaf-model). -/
def presheafFactors (L : CochainComplex (A.{uC, vC, u} J R) ℤ) (n : ℤ) :
    DerivedCategory.Q ⋙ presheaf.{uC, vC, u, w} J R L n ≅
      homPresheaf.{uC, vC, u} J R L ⋙
        HomologicalComplex.homologyFunctor (B.{uC, vC, u} J R) (.up ℤ) n :=
  Localization.fac _ (presheaf_homology_inverts.{uC, vC, u} J R L n) _

/-- Concrete interface for the resolved local Hom construction.
Source: Stacks Project, Tags 0A8Y and 0A95.
(blueprint: lem-per-local-rhom-presheaf-model). -/
def forgetSheafificationIso :
    SheafOfModules.forget (rings.{uC, vC, u} J R) ⋙ sh.{uC, vC, u} J R ≅
      𝟭 (A.{uC, vC, u} J R) :=
  asIso (PresheafOfModules.sheafificationAdjunction.{max uC vC u}
    (𝟙 (rings.{uC, vC, u} J R).obj)).counit

/-- Concrete interface for the resolved local Hom construction.
Source: Stacks Project, Tags 0A8Y and 0A95.
(blueprint: lem-per-local-rhom-presheaf-model). -/
def homologySheafificationIso (n : ℤ) :
    (SheafOfModules.forget (rings.{uC, vC, u} J R)).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (B.{uC, vC, u} J R) (.up ℤ) n ⋙
          sh.{uC, vC, u} J R ≅
      HomologicalComplex.homologyFunctor (A.{uC, vC, u} J R) (.up ℤ) n := by
  let F := (SheafOfModules.forget (rings.{uC, vC, u} J R)).mapHomologicalComplex
    (.up ℤ)
  let H := HomologicalComplex.homologyFunctor (A.{uC, vC, u} J R) (.up ℤ) n
  let c := NatIso.mapHomologicalComplex
    (forgetSheafificationIso.{uC, vC, u} J R) (.up ℤ)
  let h : F ⋙ HomologicalComplex.homologyFunctor (B.{uC, vC, u} J R) (.up ℤ) n ⋙
      sh.{uC, vC, u} J R ≅
      F ⋙ (sh.{uC, vC, u} J R).mapHomologicalComplex (.up ℤ) ⋙ H :=
    Functor.isoWhiskerLeft
      (F ⋙ HomologicalComplex.shortComplexFunctor (B.{uC, vC, u} J R) (.up ℤ) n)
      (ShortComplex.homologyFunctorIso (sh.{uC, vC, u} J R)).symm
  exact h ≪≫ Functor.isoWhiskerRight c H

/-- Concrete interface for the resolved local Hom construction.
Source: Stacks Project, Tags 0A8Y and 0A95.
(blueprint: lem-per-local-rhom-presheaf-model). -/
def representativeIso (L : CochainComplex (A.{uC, vC, u} J R) ℤ) :
    DerivedCategory.Q ⋙ RH.{uC, vC, u, w} J R (DerivedCategory.Q.obj L) ≅
      WeilConjectures.coefficientHomResolution.{u, uC, vC} J R ⋙
        (homComplexFunctor.{uC, vC, max uC vC u, max uC vC u} (R := R)).obj (op L) ⋙
          DerivedCategory.Q := by
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{uC, vC, u} J R).1
  let e := Localization.fac _
    (derivedInternalHomOfUniverses_inverts.{uC, vC, u, w} J R _
      (CochainComplex.toKInjectiveResolution.{max uC vC u} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max uC vC u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max uC vC u} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)
  let e' := (Functor.curry.mapIso e).app (op L)
  let α := (Functor.curryObjProdComp DerivedCategory.Q.op DerivedCategory.Q
    (derivedInternalHomOfUniverses.{uC, vC, u, w} J R)).app (op L)
  let β : (Functor.curry.obj
      ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{max uC vC u} _) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q)).obj
      (op L) ≅
        WeilConjectures.coefficientHomResolution.{u, uC, vC} J R ⋙
          (homComplexFunctor (R := R)).obj (op L) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
      dsimp
      simp only [Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id]
      rfl)
  exact α.symm ≪≫ e' ≪≫ β

/-- The fixed comparison on a K-injective target, normalized by the resolution map.
Source: Stacks Project, Tag 0A94.
(blueprint: lem-per-local-rhom-presheaf-model). -/
def kInjectiveRepresentativeIso
    (L I : CochainComplex (A.{uC, vC, u} J R) ℤ) [I.IsKInjective] :
    (RH.{uC, vC, u, w} J R (DerivedCategory.Q.obj L)).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj
        (homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) L I) := by
  have :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{uC, vC, u} J R).1
  let η := (CochainComplex.toKInjectiveResolution.{max uC vC u} (A.{uC, vC, u} J R)).app I
  have : QuasiIso η := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ I).2
  have : ((WeilConjectures.coefficientHomResolution.{u, uC, vC} J R).obj I).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max uC vC u} _ I
  have : QuasiIso (homAugmentation.{uC, vC, u} J R L I) := by
    simpa [homAugmentation, η] using
      (quasiIso_homComplex_mapOfUniverses.{uC, vC, u} (R := R) (I' := I)
        (I := (WeilConjectures.coefficientHomResolution.{u, uC, vC} J R).obj I)
        (L' := L) (L := L) η (𝟙 L))
  exact WeilConjectures.coefficientHomResolutionIso.{u, uC, vC, w} J R L I ≪≫
    (asIso (DerivedCategory.Q.map (homAugmentation.{uC, vC, u} J R L I))).symm

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))] in
/-- The representative comparison satisfies its augmentation normalization.
Source: Stacks Project, Tag 0A94.
(blueprint: lem-per-local-rhom-presheaf-model). -/
theorem kInjectiveRepresentativeIso_normalization
    (L I : CochainComplex (A.{uC, vC, u} J R) ℤ) [I.IsKInjective] :
    (kInjectiveRepresentativeIso.{uC, vC, u, w} J R L I).hom ≫
      DerivedCategory.Q.map (homAugmentation.{uC, vC, u} J R L I) =
        (WeilConjectures.coefficientHomResolutionIso.{u, uC, vC, w} J R L I).hom := by
  simp [kInjectiveRepresentativeIso]

/-- Sheafifying resolved local cohomology recovers internal derived Hom cohomology.
Source: Stacks Project, Tags 03EI and 0A95.
(blueprint: lem-per-local-rhom-presheaf-model). -/
def sheafificationIso (L : CochainComplex (A.{uC, vC, u} J R) ℤ) (n : ℤ) :
    presheaf.{uC, vC, u, w} J R L n ⋙ sh.{uC, vC, u} J R ≅
      T.{uC, vC, u, w} J R (DerivedCategory.Q.obj L) n := by
  let F := WeilConjectures.coefficientHomResolution.{u, uC, vC} J R ⋙
    (homComplexFunctor.{uC, vC, max uC vC u, max uC vC u} (R := R)).obj (op L)
  let H := DerivedCategory.homologyFunctor (A.{uC, vC, u} J R) n
  let e₁ := Functor.isoWhiskerRight
    (presheafFactors.{uC, vC, u, w} J R L n) (sh.{uC, vC, u} J R)
  let e₂ := Functor.isoWhiskerLeft F (homologySheafificationIso.{uC, vC, u} J R n)
  let e₃ := Functor.isoWhiskerLeft F (DerivedCategory.homologyFunctorFactors _ n)
  let e₄ := Functor.isoWhiskerRight (representativeIso.{uC, vC, u, w} J R L) H
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (A.{uC, vC, u} J R) (.up ℤ)) _).preimageIso
      (e₁ ≪≫ e₂ ≪≫ e₃.symm ≪≫ e₄.symm)

/-- Evaluation commutes with the homology of a module-presheaf complex.
Source: Stacks Project, Modules on Sites, section on presheaves of modules.
(blueprint: lem-per-local-rhom-presheaf-model). -/
def evaluationHomologyIso
    (H : CochainComplex (B.{uC, vC, u} J R) ℤ) (n : ℤ) (U : C) :
    (((PresheafOfModules.evaluation (rings.{uC, vC, u} J R).obj (op U) ⋙
      forget₂ (ModuleCat.{max uC vC u} ((rings.{uC, vC, u} J R).obj.obj (op U)))
        AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj H).homology n ≅
      (PresheafOfModules.evaluation (rings.{uC, vC, u} J R).obj (op U) ⋙
        forget₂ (ModuleCat.{max uC vC u} ((rings.{uC, vC, u} J R).obj.obj (op U)))
          AddCommGrpCat).obj (H.homology n) :=
  (H.sc n).mapHomologyIso
    (PresheafOfModules.evaluation (rings.{uC, vC, u} J R).obj (op U) ⋙
      forget₂ (ModuleCat.{max uC vC u} ((rings.{uC, vC, u} J R).obj.obj (op U))) AddCommGrpCat)

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))] in
/-- The descended sheafification comparison has the specified factorization on complexes.
Source: Stacks Project, Tags 03EI and 0A95.
(blueprint: lem-per-local-rhom-presheaf-model). -/
theorem sheafificationIso_onQ (L X : CochainComplex (A.{uC, vC, u} J R) ℤ) (n : ℤ) :
    (sheafificationIso.{uC, vC, u, w} J R L n).hom.app (DerivedCategory.Q.obj X) =
      (sh.{uC, vC, u} J R).map ((presheafFactors.{uC, vC, u, w} J R L n).hom.app X) ≫
        (homologySheafificationIso.{uC, vC, u} J R n).hom.app
          (homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) L
            ((WeilConjectures.coefficientHomResolution.{u, uC, vC} J R).obj X)) ≫
        (DerivedCategory.homologyFunctorFactors (A.{uC, vC, u} J R) n).inv.app _ ≫
        (DerivedCategory.homologyFunctor (A.{uC, vC, u} J R) n).map
          ((representativeIso.{uC, vC, u, w} J R L).inv.app X) := by
  exact congr_app ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (A.{uC, vC, u} J R) (.up ℤ)) _).map_preimage _) X

/-- The natural comparison with internal Hom cohomology on any source representative.
Source: Stacks Project, Tag 0A95.
(blueprint: lem-per-local-rhom-presheaf-model). -/
def sheafificationIsoOfRepresentative
    (K : D.{uC, vC, u, w} J R) (L : CochainComplex (A.{uC, vC, u} J R) ℤ)
    (k : DerivedCategory.Q.obj L ≅ K) (n : ℤ) :
    presheaf.{uC, vC, u, w} J R L n ⋙ sh.{uC, vC, u} J R ≅
      T.{uC, vC, u, w} J R K n :=
  sheafificationIso.{uC, vC, u, w} J R L n ≪≫
    Functor.isoWhiskerRight
      ((Functor.curry.obj (derivedInternalHomOfUniverses.{uC, vC, u, w} J R)).mapIso
        k.symm.op) (DerivedCategory.homologyFunctor (A.{uC, vC, u} J R) n)

end CategoryTheory.LocalRHom.Model
