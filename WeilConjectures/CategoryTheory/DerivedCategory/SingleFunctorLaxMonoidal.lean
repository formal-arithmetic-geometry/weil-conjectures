/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-! # The canonical lax tensor structure on the derived degree-zero functor -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

variable {A : Type v} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

/-- The canonical tensor comparison for objects placed in degree zero. It is the lax
localization tensorator followed by the total-tensor/single-complex identification.
Source: Stacks Project, Tags 06YQ and 08JJ
(blueprint: lem-pod-single-functor-lax-monoidal). -/
def singleFunctorTensorComparison (P Q : A) :
    (singleFunctor A 0).obj P ⊗ (singleFunctor A 0).obj Q ⟶
      (singleFunctor A 0).obj (P ⊗ Q) :=
  (((singleFunctorIsoCompQ A 0).app P).hom ⊗ₘ
      ((singleFunctorIsoCompQ A 0).app Q).hom) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      ((CochainComplex.singleFunctor A 0).obj P)
      ((CochainComplex.singleFunctor A 0).obj Q) ≫
    DerivedCategory.Q.map
      (((CochainComplex.map₂HomologicalComplexFlipObjSingleIso
        (curriedTensor A) Q).app ((CochainComplex.singleFunctor A 0).obj P) ≪≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorRight Q) (.up ℤ) 0).app P).hom) ≫
    ((singleFunctorIsoCompQ A 0).app (P ⊗ Q)).inv

omit [Abelian.HasFunctorialFlatResolution A] in
private lemma singleCochainTensorIso_eq_flip (P Q : A) :
    AlgebraicGeometry.Etale.singleCochainTensorIso P Q =
      ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso
        (curriedTensor A) Q).app ((CochainComplex.singleFunctor A 0).obj P) ≪≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorRight Q) (.up ℤ) 0).app P) := by
  apply Iso.ext_inv
  apply HomologicalComplex.from_single_hom_ext
  simp [AlgebraicGeometry.Etale.singleCochainTensorIso,
    CochainComplex.mapBifunctorSingle₁Iso_inv_f, CochainComplex.mapBifunctorSingle₂Iso_inv_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.single, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors, whiskerLeft_id]

omit [Abelian.HasFunctorialFlatResolution A] in
private lemma singleCochain_unit
    (m : (HomologicalComplex.single A (.up ℤ) 0).Monoidal)
    (hm : ∀ P Q : A, letI := m;
      Functor.LaxMonoidal.μ (HomologicalComplex.single A (.up ℤ) 0) P Q =
        (AlgebraicGeometry.Etale.singleCochainTensorIso P Q).hom) :
    letI := m;
    Functor.LaxMonoidal.ε (HomologicalComplex.single A (.up ℤ) 0) = 𝟙 _ := by
  let := m
  let sg := HomologicalComplex.single A (.up ℤ) 0
  have h := Functor.LaxMonoidal.left_unitality sg (𝟙_ A)
  rw [hm] at h
  have hi (L M : A) :
      (AlgebraicGeometry.Etale.singleCochainTensorIso L M).inv.f 0 =
        HomologicalComplex.ιTensorObj (sg.obj L) (sg.obj M) 0 0 0 rfl := by
    simp [AlgebraicGeometry.Etale.singleCochainTensorIso,
      CochainComplex.mapBifunctorSingle₁Iso_inv_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      HomologicalComplex.single, whiskerLeft_id, sg]
  have hμiso : AlgebraicGeometry.Etale.singleCochainTensorIso (𝟙_ A) (𝟙_ A) ≪≫
      sg.mapIso (λ_ (𝟙_ A)) = λ_ (sg.obj (𝟙_ A)) := by
    apply Iso.ext_inv
    apply HomologicalComplex.from_single_hom_ext
    change _ = (HomologicalComplex.leftUnitor' (sg.obj (𝟙_ A))).inv 0
    simp [Iso.trans_inv, Functor.mapIso_inv, HomologicalComplex.comp_f, hi,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      HomologicalComplex.single, HomologicalComplex.tensorUnit,
      HomologicalComplex.leftUnitor'_inv, sg]
  have hμ := congrArg Iso.hom hμiso
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hμ
  rw [hμ] at h
  have he : Functor.LaxMonoidal.ε sg ▷ sg.obj (𝟙_ A) = 𝟙 _ := by
    apply (cancel_mono (λ_ (sg.obj (𝟙_ A))).hom).1
    simpa only [Category.id_comp] using h.symm
  apply (cancel_epi (ρ_ (𝟙_ (CochainComplex A ℤ)) ).hom).1
  rw [← rightUnitor_naturality]
  simp only [Category.comp_id]
  change Functor.LaxMonoidal.ε sg ▷ sg.obj (𝟙_ A) ≫
      (ρ_ (sg.obj (𝟙_ A))).hom = (ρ_ (sg.obj (𝟙_ A))).hom
  simpa only [Category.id_comp] using
    congrArg (fun f ↦ f ≫ (ρ_ (sg.obj (𝟙_ A))).hom) he

/-- The degree-zero functor has the canonical lax tensorator and the canonical unit map.
Source: Stacks Project, Tags 06YQ and 08JJ
(blueprint: lem-pod-single-functor-lax-monoidal).
Proof: use the monoidal functor taking an object to its degree-zero cochain complex,
then lax monoidal localization. Transport along the natural single/localization
isomorphism. The two single/total tensor formulas agree on the unique nonzero
summand (0,0); the unit formula follows from the cochain unit equation and the
localization unit comparison. -/
theorem exists_singleFunctorLaxMonoidal :
    ∃ m : (singleFunctor A 0).LaxMonoidal,
      (∀ P Q : A, letI := m;
        Functor.LaxMonoidal.μ (singleFunctor A 0) P Q = singleFunctorTensorComparison P Q) ∧
      (letI := m;
        Functor.LaxMonoidal.ε (singleFunctor A 0) = (singleFunctorObjUnitIso A).inv) := by
  obtain ⟨ms, hms⟩ := AlgebraicGeometry.Etale.exists_singleCochainMonoidal (C := A)
  let : (CochainComplex.singleFunctor A 0).Monoidal := ms
  have hms' (P Q : A) :
      Functor.LaxMonoidal.μ (CochainComplex.singleFunctor A 0) P Q =
        (AlgebraicGeometry.Etale.singleCochainTensorIso P Q).hom := by
    simpa only [CochainComplex.singleFunctor, CochainComplex.singleFunctors] using hms P Q
  have hus : Functor.LaxMonoidal.ε (CochainComplex.singleFunctor A 0) = 𝟙 _ := by
    simpa only [CochainComplex.singleFunctor, CochainComplex.singleFunctors] using
      singleCochain_unit ms hms
  let e := singleFunctorIsoCompQ A 0
  let m := Functor.LaxMonoidal.transport e.symm
  refine ⟨m, ?_, ?_⟩
  · intro P Q
    rw [Functor.LaxMonoidal.transport_μ]
    simp only [Functor.LaxMonoidal.comp_μ, hms', Functor.comp_obj, Category.assoc,
      Iso.symm_hom, Iso.symm_inv]
    rw [singleCochainTensorIso_eq_flip]
    rfl
  · rw [Functor.LaxMonoidal.transport_ε]
    simp only [Functor.LaxMonoidal.comp_ε, hus]
    simp [singleFunctorObjUnitIso, Iso.trans_inv, Functor.LaxMonoidal.transport_ε,
      Functor.LaxMonoidal.comp_ε, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors]
    rfl

end DerivedCategory
