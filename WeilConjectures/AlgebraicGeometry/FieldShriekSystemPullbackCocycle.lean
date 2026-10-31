/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemModels
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemCoherence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! # Normalized whole-system pullback comparison cocycle

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md (2), coefficient composition and identity
(blueprint: lem-route-field-shriek-system-pullback-cocycle).

The equalities are of natural transformations on ordinary unbounded derived categories
of whole coefficient systems. No finite evaluation or constructibility restriction occurs.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u c v r c' v'

open CategoryTheory AlgebraicGeometry WeilConjectures
open CategoryTheory.Functor WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

attribute [local irreducible] coefficientMap HasDerivedCategory.standard scalarAssoc scalarUnit

private theorem mate_composition
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {a₀ : A₀ ⥤ A₁} {a₁ : A₁ ⥤ A₂} {a₂ : A₀ ⥤ A₂}
    {b₀ : B₀ ⥤ B₁} {b₁ : B₁ ⥤ B₂} {b₂ : B₀ ⥤ B₂}
    {v₀ : A₀ ⥤ B₀} {v₁ : A₁ ⥤ B₁} {v₂ : A₂ ⥤ B₂}
    {ra₀ : A₁ ⥤ A₀} {ra₁ : A₂ ⥤ A₁} {ra₂ : A₂ ⥤ A₀}
    {rb₀ : B₁ ⥤ B₀} {rb₁ : B₂ ⥤ B₁} {rb₂ : B₂ ⥤ B₀}
    {h₀ : B₀ ⥤ A₀} {h₁ : B₁ ⥤ A₁} {h₂ : B₂ ⥤ A₂}
    (aa₀ : a₀ ⊣ ra₀) (aa₁ : a₁ ⊣ ra₁) (aa₂ : a₂ ⊣ ra₂)
    (ab₀ : b₀ ⊣ rb₀) (ab₁ : b₁ ⊣ rb₁) (ab₂ : b₂ ⊣ rb₂)
    (av₀ : v₀ ⊣ h₀) (av₁ : v₁ ⊣ h₁) (av₂ : v₂ ⊣ h₂)
    (χ₀ : a₀ ⋙ v₁ ≅ v₀ ⋙ b₀) (χ₁ : a₁ ⋙ v₂ ≅ v₁ ⋙ b₁)
    (χ₂ : a₂ ⋙ v₂ ≅ v₀ ⋙ b₂)
    (α : a₀ ⋙ a₁ ≅ a₂) (β : b₀ ⋙ b₁ ≅ b₂)
    (ρ₀ : rb₀ ⋙ h₀ ≅ h₁ ⋙ ra₀) (ρ₁ : rb₁ ⋙ h₁ ≅ h₂ ⋙ ra₁)
    (ρ₂ : rb₂ ⋙ h₀ ≅ h₂ ⋙ ra₂)
    (rA : ra₁ ⋙ ra₀ ≅ ra₂) (rB : rb₁ ⋙ rb₀ ≅ rb₂)
    (hχ₀ : conjugateIsoEquiv (av₀.comp ab₀) (aa₀.comp av₁) χ₀ = ρ₀)
    (hχ₁ : conjugateIsoEquiv (av₁.comp ab₁) (aa₁.comp av₂) χ₁ = ρ₁)
    (hχ₂ : conjugateIsoEquiv (av₀.comp ab₂) (aa₂.comp av₂) χ₂ = ρ₂)
    (hα : conjugateIsoEquiv aa₂ (aa₀.comp aa₁) α = rA.symm)
    (hβ : conjugateIsoEquiv ab₂ (ab₀.comp ab₁) β = rB.symm)
    (hr : whiskerRight rB.inv h₀ ≫ whiskerLeft rb₁ ρ₀.hom ≫
        whiskerRight ρ₁.hom ra₀ = ρ₂.hom ≫ whiskerLeft h₂ rA.inv) :
    whiskerLeft a₀ χ₁.hom ≫ whiskerRight χ₀.hom b₁ ≫ whiskerLeft v₀ β.hom =
      whiskerRight α.hom v₂ ≫ χ₂.hom := by
  let lhs := associator a₀ a₁ v₂ ≪≫ isoWhiskerLeft a₀ χ₁ ≪≫
    (associator a₀ v₁ b₁).symm ≪≫ isoWhiskerRight χ₀ b₁ ≪≫
      associator v₀ b₀ b₁ ≪≫ isoWhiskerLeft v₀ β
  let rhs := isoWhiskerRight α v₂ ≪≫ χ₂
  have he : lhs = rhs := by
    apply (conjugateIsoEquiv (av₀.comp ab₂) ((aa₀.comp aa₁).comp av₂)).injective
    dsimp only [lhs, rhs]
    simp only [← Iso.trans_assoc]
    rw [conjugateIsoEquiv_trans (av₀.comp ab₂) (av₀.comp (ab₀.comp ab₁))
      ((aa₀.comp aa₁).comp av₂)]
    rw [conjugateIsoEquiv_isoWhiskerLeft, hβ]
    rw [conjugateIsoEquiv_trans (av₀.comp (ab₀.comp ab₁))
      ((av₀.comp ab₀).comp ab₁) ((aa₀.comp aa₁).comp av₂)]
    rw [conjugateIsoEquiv_associator]
    rw [conjugateIsoEquiv_trans ((av₀.comp ab₀).comp ab₁)
      ((aa₀.comp av₁).comp ab₁) ((aa₀.comp aa₁).comp av₂)]
    rw [conjugateIsoEquiv_isoWhiskerRight, hχ₀]
    rw [conjugateIsoEquiv_trans ((aa₀.comp av₁).comp ab₁)
      (aa₀.comp (av₁.comp ab₁)) ((aa₀.comp aa₁).comp av₂)]
    rw [conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_associator]
    rw [conjugateIsoEquiv_trans (aa₀.comp (av₁.comp ab₁))
      (aa₀.comp (aa₁.comp av₂)) ((aa₀.comp aa₁).comp av₂)]
    rw [conjugateIsoEquiv_isoWhiskerLeft, hχ₁, conjugateIsoEquiv_associator]
    rw [conjugateIsoEquiv_trans (av₀.comp ab₂) (aa₂.comp av₂)
      ((aa₀.comp aa₁).comp av₂), hχ₂, conjugateIsoEquiv_isoWhiskerRight, hα]
    apply Iso.ext
    ext M
    have hh := congr_app hr M
    simpa only [Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
      Category.assoc] using hh
  ext M
  have hh := congrArg (fun i ↦ i.hom.app M) he
  simpa only [lhs, rhs, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc] using hh

private theorem mate_unit
    {A B : Type*} [Category A] [Category B]
    {a : A ⥤ A} {b : B ⥤ B} {v : A ⥤ B}
    {ra : A ⥤ A} {rb : B ⥤ B} {h : B ⥤ A}
    (aa : a ⊣ ra) (ab : b ⊣ rb) (av : v ⊣ h)
    (χ : a ⋙ v ≅ v ⋙ b) (α : a ≅ 𝟭 _) (β : b ≅ 𝟭 _)
    (ρ : rb ⋙ h ≅ h ⋙ ra) (rA : ra ≅ 𝟭 _) (rB : rb ≅ 𝟭 _)
    (hχ : conjugateIsoEquiv (av.comp ab) (aa.comp av) χ = ρ)
    (hα : conjugateIsoEquiv Adjunction.id aa α = rA.symm)
    (hβ : conjugateIsoEquiv Adjunction.id ab β = rB.symm)
    (hr : whiskerRight rB.inv h ≫ ρ.hom = whiskerLeft h rA.inv) :
    χ.hom ≫ whiskerLeft v β.hom = whiskerRight α.hom v := by
  let lhs := χ ≪≫ isoWhiskerLeft v β ≪≫ rightUnitor v
  let rhs := isoWhiskerRight α v ≪≫ leftUnitor v
  have he : lhs = rhs := by
    apply (conjugateIsoEquiv av (aa.comp av)).injective
    dsimp only [lhs, rhs]
    simp only [← Iso.trans_assoc]
    conv_lhs =>
      rw [conjugateIsoEquiv_trans av (av.comp Adjunction.id) (aa.comp av),
        conjugateIsoEquiv_rightUnitor]
      rw [conjugateIsoEquiv_trans (av.comp Adjunction.id) (av.comp ab) (aa.comp av),
        conjugateIsoEquiv_isoWhiskerLeft, hβ, hχ]
    conv_rhs =>
      rw [conjugateIsoEquiv_trans av (Adjunction.id.comp av) (aa.comp av),
        conjugateIsoEquiv_leftUnitor, conjugateIsoEquiv_isoWhiskerRight, hα]
    apply Iso.ext
    ext M
    have hh := congr_app hr M
    simpa only [Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      leftUnitor_inv_app, rightUnitor_inv_app, Category.id_comp, Category.comp_id,
      Category.assoc] using hh
  ext M
  have hh := congrArg (fun i ↦ i.hom.app M) he
  simpa only [lhs, rhs, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    leftUnitor_hom_app, rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id,
    Category.assoc] using hh

private theorem composition_coordinates
    {A B C X Y Z DA DB DC DX DY DZ : Type*}
    [Category A] [Category B] [Category C] [Category X] [Category Y] [Category Z]
    [Category DA] [Category DB] [Category DC] [Category DX] [Category DY] [Category DZ]
    (QA : A ⥤ DA) (QB : B ⥤ DB) (QC : C ⥤ DC)
    (QX : X ⥤ DX) (QY : Y ⥤ DY) (QZ : Z ⥤ DZ)
    (a : A ⥤ B) (b : B ⥤ C) (c : A ⥤ C)
    (x : X ⥤ Y) (y : Y ⥤ Z) (z : X ⥤ Z)
    (v : A ⥤ X) (w : B ⥤ Y) (t : C ⥤ Z)
    (ad : DA ⥤ DB) (bd : DB ⥤ DC) (cd : DA ⥤ DC)
    (xd : DX ⥤ DY) (yd : DY ⥤ DZ) (zd : DX ⥤ DZ)
    (vd : DA ⥤ DX) (wd : DB ⥤ DY) (td : DC ⥤ DZ)
    (ea : QA ⋙ ad ⟶ a ⋙ QB) (eb : QB ⋙ bd ⟶ b ⋙ QC) (ec : QA ⋙ cd ⟶ c ⋙ QC)
    (ex : QX ⋙ xd ⟶ x ⋙ QY) (ey : QY ⋙ yd ⟶ y ⋙ QZ) (ez : QX ⋙ zd ⟶ z ⋙ QZ)
    (iv : QA ⋙ vd ⟶ v ⋙ QX) (iw : QB ⋙ wd ⟶ w ⋙ QY) (it : QC ⋙ td ⟶ t ⋙ QZ)
    (la : ad ⋙ wd ⟶ vd ⋙ xd) (lb : bd ⋙ td ⟶ wd ⋙ yd) (lc : cd ⋙ td ⟶ vd ⋙ zd)
    (oa : a ⋙ w ⟶ v ⋙ x) (ob : b ⋙ t ⟶ w ⋙ y) (oc : c ⋙ t ⟶ v ⋙ z)
    (α : ad ⋙ bd ⟶ cd) (β : xd ⋙ yd ⟶ zd)
    (αo : a ⋙ b ⟶ c) (βo : x ⋙ y ⟶ z)
    (ha : ∀ K, la.app (QA.obj K) ≫ xd.map (iv.app K) ≫ ex.app (v.obj K) =
      wd.map (ea.app K) ≫ iw.app (a.obj K) ≫ QY.map (oa.app K))
    (hb : ∀ K, lb.app (QB.obj K) ≫ yd.map (iw.app K) ≫ ey.app (w.obj K) =
      td.map (eb.app K) ≫ it.app (b.obj K) ≫ QZ.map (ob.app K))
    (hc : ∀ K, lc.app (QA.obj K) ≫ zd.map (iv.app K) ≫ ez.app (v.obj K) =
      td.map (ec.app K) ≫ it.app (c.obj K) ≫ QZ.map (oc.app K))
    (hα : ∀ K, α.app (QA.obj K) ≫ ec.app K =
      bd.map (ea.app K) ≫ eb.app (a.obj K) ≫ QC.map (αo.app K))
    (hβ : ∀ K, β.app (QX.obj K) ≫ ez.app K =
      yd.map (ex.app K) ≫ ey.app (x.obj K) ≫ QZ.map (βo.app K))
    (ho : ∀ K, ob.app (a.obj K) ≫ y.map (oa.app K) ≫ βo.app (v.obj K) =
      t.map (αo.app K) ≫ oc.app K)
    (K : A) :
    (lb.app (ad.obj (QA.obj K)) ≫ yd.map (la.app (QA.obj K)) ≫
        β.app (vd.obj (QA.obj K))) ≫ zd.map (iv.app K) ≫ ez.app (v.obj K) =
      (td.map (α.app (QA.obj K)) ≫ lc.app (QA.obj K)) ≫
        zd.map (iv.app K) ≫ ez.app (v.obj K) := by
  have nβ := β.naturality (iv.app K)
  have ney := ey.naturality (oa.app K)
  have nlb := lb.naturality (ea.app K)
  have nit := it.naturality (αo.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at nβ ney nlb nit
  simp only [Category.assoc]
  rw [← reassoc_of% nβ, hβ]
  simp only [← yd.map_comp_assoc]
  rw [ha]
  simp only [yd.map_comp, Category.assoc]
  rw [← reassoc_of% nlb, reassoc_of% ney]
  rw [reassoc_of% (hb (a.obj K))]
  rw [← QZ.map_comp, ← QZ.map_comp, ho]
  simp only [QZ.map_comp]
  rw [← reassoc_of% nit]
  simp only [← td.map_comp_assoc]
  rw [← hα, td.map_comp, Category.assoc]
  rw [hc]

private theorem unit_coordinates
    {A X DA DX : Type*} [Category A] [Category X] [Category DA] [Category DX]
    (QA : A ⥤ DA) (QX : X ⥤ DX) (a : A ⥤ A) (x : X ⥤ X) (v : A ⥤ X)
    (ad : DA ⥤ DA) (xd : DX ⥤ DX) (vd : DA ⥤ DX)
    (ea : QA ⋙ ad ⟶ a ⋙ QA) (ex : QX ⋙ xd ⟶ x ⋙ QX)
    (iv : QA ⋙ vd ⟶ v ⋙ QX) (la : ad ⋙ vd ⟶ vd ⋙ xd)
    (oa : a ⋙ v ⟶ v ⋙ x)
    (α : ad ⟶ 𝟭 _) (β : xd ⟶ 𝟭 _) (αo : a ⟶ 𝟭 _) (βo : x ⟶ 𝟭 _)
    (ha : ∀ K, la.app (QA.obj K) ≫ xd.map (iv.app K) ≫ ex.app (v.obj K) =
      vd.map (ea.app K) ≫ iv.app (a.obj K) ≫ QX.map (oa.app K))
    (hα : ∀ K, α.app (QA.obj K) = ea.app K ≫ QA.map (αo.app K))
    (hβ : ∀ K, β.app (QX.obj K) = ex.app K ≫ QX.map (βo.app K))
    (ho : ∀ K, oa.app K ≫ βo.app (v.obj K) = v.map (αo.app K))
    (K : A) :
    (la.app (QA.obj K) ≫ β.app (vd.obj (QA.obj K))) ≫ iv.app K =
      vd.map (α.app (QA.obj K)) ≫ iv.app K := by
  have nβ := β.naturality (iv.app K)
  have niv := iv.naturality (αo.app K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at nβ niv
  rw [Category.assoc, ← nβ, hβ]
  rw [reassoc_of% (ha K)]
  rw [← QX.map_comp, ho, ← niv, hα, vd.map_comp]
  simp only [Category.assoc]

section

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
-- A resolving map is invertible at the source of the transpose formula.
private theorem transpose_all (A : ScalarData φ)
    (P : CochainComplex (Mod J R) ℤ) (K : CochainComplex (Mod J S) ℤ)
    (f : (A.model.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    A.adjunction.homEquiv _ _ (A.model.ε.app P ≫ DerivedCategory.Q.map f) ≫
        (res φ).mapDerivedCategoryFactors.hom.app K =
      DerivedCategory.Q.map
        ((A.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) := by
  obtain ⟨L, q, hL, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
  have : QuasiIso q := hq
  let a := A.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)
  let F := A.model.E.mapHomologicalComplex (.up ℤ)
  have h := A.transpose_model L K hL (F.map q ≫ f)
  apply (cancel_epi (DerivedCategory.Q.map q)).mp
  calc
    _ = A.adjunction.homEquiv _ _
        (A.T.map (DerivedCategory.Q.map q) ≫ A.model.ε.app P ≫
          DerivedCategory.Q.map f) ≫ (res φ).mapDerivedCategoryFactors.hom.app K := by
      rw [A.adjunction.homEquiv_naturality_left, Category.assoc]
    _ = A.adjunction.homEquiv _ _
        (A.model.ε.app L ≫ DerivedCategory.Q.map (F.map q ≫ f)) ≫
          (res φ).mapDerivedCategoryFactors.hom.app K := by
      rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
      have hn := A.model.ε.naturality q
      dsimp only [Functor.comp_map] at hn
      rw [hn]
    _ = DerivedCategory.Q.map (a.homEquiv _ _ (F.map q ≫ f)) := h
    _ = _ := by
      rw [a.homEquiv_naturality_left, Functor.map_comp]

set_option maxHeartbeats 1000000 in
-- Elaborating the ringed sequence-site functors needs a larger local budget.
-- Keep all the original scalar data; supply its unrestricted transpose normalization.
private def asSystem (A : ScalarData φ) : SheafOfModules.SystemScalarModel.{c, v, r} φ where
  model := A.model
  ordinaryAdj := A.ordinaryAdjunction
  unit_normalized := by
    intro M U x
    dsimp only [SheafOfModules.systemModelTmul]
    rw [one_smul]
    change ((A.ordinaryAdjunction.unit.app M).val.app U) x =
      ((eqToHom (A.model.obj_eq M).symm).val.app U) (extensionUnit φ M U x)
    rw [← A.unit_section M U x]
    change ((A.ordinaryAdjunction.unit.app M).val.app U) x =
      (((eqToIso (A.model.obj_eq M)).hom ≫ (eqToIso (A.model.obj_eq M)).inv).val.app U)
        (((A.ordinaryAdjunction.unit.app M).val.app U) x)
    rw [Iso.hom_inv_id]
    rfl
  adjunction := A.adjunction
  transpose := by
    intro P K f
    apply (cancel_mono ((res φ).mapDerivedCategoryFactors.hom.app K)).mp
    rw [Category.assoc, Iso.inv_hom_id_app]
    simpa only [Functor.comp_obj, Category.comp_id] using transpose_all φ A P K f

end

section

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{r} C]
  {C' : Type c'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  [EssentiallySmall.{r} C']
  {R S T : Sheaf J CommRingCat.{r}} {R' S' T' : Sheaf J' CommRingCat.{r}}

private theorem restriction_composition
    (φ : R ⟶ S) (ψ : S ⟶ T) (γ : R ⟶ T)
    (φ' : R' ⟶ S') (ψ' : S' ⟶ T') (γ' : R' ⟶ T')
    (hγ : γ = φ ≫ ψ) (hγ' : γ' = φ' ≫ ψ')
    (HE : Mod J' R' ⥤ Mod J R) (HF : Mod J' S' ⥤ Mod J S)
    (HL : Mod J' T' ⥤ Mod J T)
    (ρ : res φ' ⋙ HE ≅ HF ⋙ res φ)
    (σ : res ψ' ⋙ HF ≅ HL ⋙ res ψ)
    (τ : res γ' ⋙ HE ≅ HL ⋙ res γ)
    (hρ : ∀ M U (x : ((res φ' ⋙ HE).obj M).val.obj U),
      HEq (((ρ.hom.app M).val.app U) x) x)
    (hσ : ∀ M U (x : ((res ψ' ⋙ HF).obj M).val.obj U),
      HEq (((σ.hom.app M).val.app U) x) x)
    (hτ : ∀ M U (x : ((res γ' ⋙ HE).obj M).val.obj U),
      HEq (((τ.hom.app M).val.app U) x) x) :
    whiskerRight
        (SheafOfModules.systemScalarRestrictionComposition φ' ψ' γ' hγ').inv HE ≫
      whiskerLeft (res ψ') ρ.hom ≫ whiskerRight σ.hom (res φ) =
      τ.hom ≫ whiskerLeft HL
        (SheafOfModules.systemScalarRestrictionComposition φ ψ γ hγ).inv := by
  subst γ γ'
  apply NatTrans.ext
  funext M
  change HE.map (𝟙 _) ≫ ρ.hom.app ((res ψ').obj M) ≫
      (res φ).map (σ.hom.app M) = τ.hom.app M ≫ 𝟙 _
  ext U x
  let N := (res φ').obj ((res ψ').obj M)
  have hid : HEq (((HE.map (𝟙 N)).val.app U) x) x := by
    exact heq_of_eq (congrArg (fun f : HE.obj N ⟶ HE.obj N ↦
      ((f.val.app U).hom) x) (HE.map_id N))
  apply eq_of_heq
  exact ((hσ M U (((ρ.hom.app ((res ψ').obj M)).val.app U)
      (((HE.map (𝟙 N)).val.app U) x))).trans
    (hρ ((res ψ').obj M) U (((HE.map (𝟙 N)).val.app U) x))).trans
      (hid.trans (hτ M U x).symm)

private theorem restriction_unit
    (φ : R ⟶ R) (φ' : R' ⟶ R') (hφ : φ = 𝟙 _) (hφ' : φ' = 𝟙 _)
    (H : Mod J' R' ⥤ Mod J R) (ρ : res φ' ⋙ H ≅ H ⋙ res φ)
    (hρ : ∀ M U (x : ((res φ' ⋙ H).obj M).val.obj U),
      HEq (((ρ.hom.app M).val.app U) x) x) :
    whiskerRight (SheafOfModules.systemScalarRestrictionUnit φ' hφ').inv H ≫ ρ.hom =
      whiskerLeft H (SheafOfModules.systemScalarRestrictionUnit φ hφ).inv := by
  subst φ φ'
  apply NatTrans.ext
  funext M
  change H.map (𝟙 _) ≫ ρ.hom.app M = 𝟙 _
  ext U x
  have hid : HEq (((H.map (𝟙 M)).val.app U) x) x := by
    exact heq_of_eq (congrArg (fun f : H.obj M ⟶ H.obj M ↦
      ((f.val.app U).hom) x) (H.map_id M))
  exact eq_of_heq ((hρ M U (((H.map (𝟙 M)).val.app U) x)).trans hid)

end

-- The recorded double-mate equation fixes the ordinary comparison uniquely.
private theorem ordinary_conjugate (P : PurityFiniteSetting.{u}) (D : Models P)
    (E F : Index P) (h : E ≤ F) {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    conjugateEquiv
      ((D.scalars E F h Y).ordinaryAdjunction.comp
        ((D.operations F).geometry g).ordinaryAdjunction)
      (((D.operations E).geometry g).ordinaryAdjunction.comp
        (D.scalars E F h Z).ordinaryAdjunction)
      (D.pull E F h g).ordinary.inv = (D.pull E F h g).restrictionPush.inv := by
  rw [← iterated_mateEquiv_conjugateEquiv]
  have hm := (D.pull E F h g).ordinary_mate
  have hm' : mateEquiv (D.scalars E F h Y).ordinaryAdjunction
      (D.scalars E F h Z).ordinaryAdjunction (D.pull E F h g).ordinary.inv =
      (mateEquiv ((D.operations F).geometry g).ordinaryAdjunction
        ((D.operations E).geometry g).ordinaryAdjunction).symm
          (D.pull E F h g).restrictionPush.inv := by
    exact congrArg (TwoSquare.mk _ _ _ _) hm
  rw [hm', Equiv.apply_symm_apply]

private theorem conjugate_uniq
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (r : R ≅ R') :
    conjugateEquiv b a ((a.ofNatIsoRight r).leftAdjointUniq b).hom = r.inv := by
  have h := conjugateEquiv_leftAdjointUniq_hom (a.ofNatIsoRight r) b
  ext X
  have hx := congr_app h X
  apply (cancel_mono (r.hom.app X)).mp
  rw [Iso.inv_hom_id_app]
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj,
    NatTrans.id_app, Category.assoc] at hx ⊢
  have hn₀ := r.hom.naturality
    (((a.ofNatIsoRight r).leftAdjointUniq b).hom.app (R'.obj X))
  have hn₁ := r.hom.naturality (b.counit.app X)
  simp only [Functor.comp_obj, Functor.id_obj] at hn₀ hn₁
  rw [← reassoc_of% hn₀, ← hn₁] at hx
  exact hx

set_option maxHeartbeats 1000000 in
-- Elaborating the ringed sequence-site functors needs a larger local budget.
-- Extend the representative equation by naturality at a K-flat resolution.
private theorem representative_all (P : PurityFiniteSetting.{u}) (D : Models P)
    (E F : Index P) (h : E ≤ F) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (K : CochainComplex (SpTowerShriek.S P.coefficients.l E.val Y) ℤ) :
    (D.pull E F h g).derived.hom.app (DerivedCategory.Q.obj K) ≫
        (D.scalars E F h Z).T.map
          (((D.operations E).geometry g).pull.mapDerivedCategoryFactors.hom.app K) ≫
        (D.scalars E F h Z).model.ε.app
          ((((D.operations E).geometry g).pull.mapHomologicalComplex (.up ℤ)).obj K) =
      (SpTowerShriek.pull P.coefficients.l F.val (D.base F) ((D.operations F).geometry g)).map
          ((D.scalars E F h Y).model.ε.app K) ≫
        ((D.operations F).geometry g).pull.mapDerivedCategoryFactors.hom.app
          (((D.scalars E F h Y).model.E.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (D.pull E F h g).ordinary.hom (.up ℤ)).app K) := by
  let AY := (D.scalars E F h Y).model.E.mapHomologicalComplex (.up ℤ)
  let VE := ((D.operations E).geometry g).pull.mapHomologicalComplex (.up ℤ)
  let cmp := (D.pull E F h g).derived.hom
  let ξE := ((D.operations E).geometry g).pull.mapDerivedCategoryFactors.hom
  let ξF := ((D.operations F).geometry g).pull.mapDerivedCategoryFactors.hom
  let G := SpTowerShriek.pull P.coefficients.l F.val (D.base F) ((D.operations F).geometry g)
  let α := Functor.whiskerLeft DerivedCategory.Q cmp ≫
    Functor.whiskerRight ξE (D.scalars E F h Z).T ≫
    Functor.whiskerLeft VE (D.scalars E F h Z).model.ε
  let β := Functor.whiskerRight (D.scalars E F h Y).model.ε G ≫
    Functor.whiskerLeft AY ξF ≫
    Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (D.pull E F h g).ordinary.hom (.up ℤ))
      DerivedCategory.Q
  obtain ⟨L, q, hL, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := systemRing (Scheme.ProEt.topology Y)
        (SpTowerShriek.B P.coefficients.l E.val Y)
        (SpTowerShriek.tau P.coefficients.l E.val Y)) K
  have : QuasiIso q := hq
  have he : α.app L = β.app L := (D.pull E F h g).representative L hL
  change α.app K = β.app K
  have nα := α.naturality q
  have nβ := β.naturality q
  dsimp only [Functor.comp_map] at nα nβ
  apply (cancel_epi (G.map ((D.scalars E F h Y).T.map (DerivedCategory.Q.map q)))).mp
  rw [nα, nβ, he]
  rfl

private theorem ordinary_iso_conjugate (P : PurityFiniteSetting.{u}) (D : Models P)
    (E F : Index P) (h : E ≤ F) {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    conjugateIsoEquiv
      (((D.operations E).geometry g).ordinaryAdjunction.comp
        (D.scalars E F h Z).ordinaryAdjunction)
      ((D.scalars E F h Y).ordinaryAdjunction.comp
        ((D.operations F).geometry g).ordinaryAdjunction)
      (D.pull E F h g).ordinary = (D.pull E F h g).restrictionPush := by
  have hi : conjugateIsoEquiv
      ((D.scalars E F h Y).ordinaryAdjunction.comp
        ((D.operations F).geometry g).ordinaryAdjunction)
      (((D.operations E).geometry g).ordinaryAdjunction.comp
        (D.scalars E F h Z).ordinaryAdjunction)
      (D.pull E F h g).ordinary.symm = (D.pull E F h g).restrictionPush.symm :=
    Iso.ext (ordinary_conjugate P D E F h g)
  have hh := congrArg Iso.symm hi
  simpa only [← conjugateIsoEquiv_iso_symm, Iso.symm_symm_eq] using hh

private noncomputable def ordinaryAssoc (P : PurityFiniteSetting.{u}) (D : Models P)
    {E F L : Index P} (h : E ≤ F) (k : F ≤ L) (T : Scheme.{u})
    (hc : coefficientMap P (D.coefficients E L (h.trans k)) T =
      coefficientMap P (D.coefficients E F h) T ≫
        coefficientMap P (D.coefficients F L k) T) :=
  SheafOfModules.systemScalarModelComposition hc
    (asSystem _ (D.scalars E F h T)) (asSystem _ (D.scalars F L k T))
    (asSystem _ (D.scalars E L (h.trans k) T))

private noncomputable def ordinaryUnit (P : PurityFiniteSetting.{u}) (D : Models P)
    (E : Index P) (T : Scheme.{u})
    (hc : coefficientMap P (D.coefficients E E le_rfl) T = 𝟙 _) :=
  SheafOfModules.systemScalarModelUnit hc (asSystem _ (D.scalars E E le_rfl T))

set_option maxHeartbeats 1000000 in
-- Elaborating the ringed sequence-site functors needs a larger local budget.
private theorem scalarAssoc_rep (P : PurityFiniteSetting.{u}) (D : Models P)
    {E F L : Index P} (h : E ≤ F) (k : F ≤ L) (T : Scheme.{u})
    (hc : coefficientMap P (D.coefficients E L (h.trans k)) T =
      coefficientMap P (D.coefficients E F h) T ≫
        coefficientMap P (D.coefficients F L k) T)
    (K : CochainComplex (SpTowerShriek.S P.coefficients.l E.val T) ℤ) :
    (scalarAssoc P D h k T hc).hom.app (DerivedCategory.Q.obj K) ≫
        (D.scalars E L (h.trans k) T).model.ε.app K =
      (D.scalars F L k T).T.map ((D.scalars E F h T).model.ε.app K) ≫
        (D.scalars F L k T).model.ε.app
          (((D.scalars E F h T).model.E.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (ordinaryAssoc P D h k T hc).hom
            (.up ℤ)).app K) := by
  unfold scalarAssoc
  exact SheafOfModules.systemScalarModelDerivedComposition_rep hc
    (asSystem _ (D.scalars E F h T)) (asSystem _ (D.scalars F L k T))
    (asSystem _ (D.scalars E L (h.trans k) T)) K

set_option maxHeartbeats 1000000 in
-- Elaborating the ringed sequence-site functors needs a larger local budget.
private theorem scalarUnit_rep (P : PurityFiniteSetting.{u}) (D : Models P)
    (E : Index P) (T : Scheme.{u})
    (hc : coefficientMap P (D.coefficients E E le_rfl) T = 𝟙 _)
    (K : CochainComplex (SpTowerShriek.S P.coefficients.l E.val T) ℤ) :
    (scalarUnit P D E T hc).hom.app (DerivedCategory.Q.obj K) =
      (D.scalars E E le_rfl T).model.ε.app K ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (ordinaryUnit P D E T hc).hom (.up ℤ)).app K) := by
  unfold scalarUnit
  exact SheafOfModules.systemScalarModelDerivedUnit_rep hc
    (asSystem _ (D.scalars E E le_rfl T)) K

set_option maxHeartbeats 1000000 in
-- Elaborating the ringed sequence-site functors needs a larger local budget.
private theorem ordinary_composition (P : PurityFiniteSetting.{u}) (D : Models P)
    (E F L : Index P) (h : E ≤ F) (k : F ≤ L) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (hcZ : coefficientMap P (D.coefficients E L (h.trans k)) Z =
      coefficientMap P (D.coefficients E F h) Z ≫
        coefficientMap P (D.coefficients F L k) Z)
    (hcY : coefficientMap P (D.coefficients E L (h.trans k)) Y =
      coefficientMap P (D.coefficients E F h) Y ≫
        coefficientMap P (D.coefficients F L k) Y) :
    whiskerLeft (D.scalars E F h Y).model.E (D.pull F L k g).ordinary.hom ≫
        whiskerRight (D.pull E F h g).ordinary.hom (D.scalars F L k Z).model.E ≫
        whiskerLeft ((D.operations E).geometry g).pull
          (ordinaryAssoc P D h k Z hcZ).hom =
      whiskerRight (ordinaryAssoc P D h k Y hcY).hom ((D.operations L).geometry g).pull ≫
        (D.pull E L (h.trans k) g).ordinary.hom := by
  apply mate_composition
    (D.scalars E F h Y).ordinaryAdjunction (D.scalars F L k Y).ordinaryAdjunction
    (D.scalars E L (h.trans k) Y).ordinaryAdjunction
    (D.scalars E F h Z).ordinaryAdjunction (D.scalars F L k Z).ordinaryAdjunction
    (D.scalars E L (h.trans k) Z).ordinaryAdjunction
    ((D.operations E).geometry g).ordinaryAdjunction
    ((D.operations F).geometry g).ordinaryAdjunction
    ((D.operations L).geometry g).ordinaryAdjunction
    (D.pull E F h g).ordinary (D.pull F L k g).ordinary
    (D.pull E L (h.trans k) g).ordinary
    (ordinaryAssoc P D h k Y hcY) (ordinaryAssoc P D h k Z hcZ)
    (D.pull E F h g).restrictionPush (D.pull F L k g).restrictionPush
    (D.pull E L (h.trans k) g).restrictionPush
    (SheafOfModules.systemScalarRestrictionComposition.{u + 1, u, u + 1} _ _ _ hcY)
    (SheafOfModules.systemScalarRestrictionComposition.{u + 1, u, u + 1} _ _ _ hcZ)
    (ordinary_iso_conjugate P D E F h g) (ordinary_iso_conjugate P D F L k g)
    (ordinary_iso_conjugate P D E L (h.trans k) g)
  · apply Iso.ext
    exact conjugate_uniq _ _ _
  · apply Iso.ext
    exact conjugate_uniq _ _ _
  · exact restriction_composition _ _ _ _ _ _ hcY hcZ _ _ _
      (D.pull E F h g).restrictionPush (D.pull F L k g).restrictionPush
      (D.pull E L (h.trans k) g).restrictionPush
      (D.pull E F h g).sections (D.pull F L k g).sections
      (D.pull E L (h.trans k) g).sections

set_option maxHeartbeats 1000000 in
-- Elaborating the ringed sequence-site functors needs a larger local budget.
private theorem ordinary_identity (P : PurityFiniteSetting.{u}) (D : Models P)
    (E : Index P) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (hiZ : coefficientMap P (D.coefficients E E le_rfl) Z = 𝟙 _)
    (hiY : coefficientMap P (D.coefficients E E le_rfl) Y = 𝟙 _) :
    (D.pull E E le_rfl g).ordinary.hom ≫
        whiskerLeft ((D.operations E).geometry g).pull (ordinaryUnit P D E Z hiZ).hom =
      whiskerRight (ordinaryUnit P D E Y hiY).hom ((D.operations E).geometry g).pull := by
  apply mate_unit (D.scalars E E le_rfl Y).ordinaryAdjunction
    (D.scalars E E le_rfl Z).ordinaryAdjunction
    ((D.operations E).geometry g).ordinaryAdjunction
    (D.pull E E le_rfl g).ordinary (ordinaryUnit P D E Y hiY)
    (ordinaryUnit P D E Z hiZ) (D.pull E E le_rfl g).restrictionPush
    (SheafOfModules.systemScalarRestrictionUnit.{u + 1, u, u + 1} _ hiY)
    (SheafOfModules.systemScalarRestrictionUnit.{u + 1, u, u + 1} _ hiZ)
    (ordinary_iso_conjugate P D E E le_rfl g)
  · apply Iso.ext
    exact conjugate_uniq _ _ _
  · apply Iso.ext
    exact conjugate_uniq _ _ _
  · exact restriction_unit _ _ hiY hiZ _ (D.pull E E le_rfl g).restrictionPush
      (D.pull E E le_rfl g).sections

set_option maxHeartbeats 1000000 in
-- Elaborating the ringed sequence-site functors needs a larger local budget.
-- Localization and resolutions detect equality on the whole derived category.
private theorem derived_ext_kflat (P : PurityFiniteSetting.{u}) (E : Index P)
    (T : Scheme.{u}) {C : Type*} [Category C]
    {F G : SpTowerShriek.D P.coefficients.l E.val T ⥤ C} (α β : F ⟶ G)
    (h : ∀ K : CochainComplex (SpTowerShriek.S P.coefficients.l E.val T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients
        (R := systemRing (Scheme.ProEt.topology T) (SpTowerShriek.B P.coefficients.l E.val T)
          (SpTowerShriek.tau P.coefficients.l E.val T)) K →
        α.app (DerivedCategory.Q.obj K) = β.app (DerivedCategory.Q.obj K)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  obtain ⟨L, q, hL, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := systemRing (Scheme.ProEt.topology T) (SpTowerShriek.B P.coefficients.l E.val T)
        (SpTowerShriek.tau P.coefficients.l E.val T)) K
  have : QuasiIso q := hq
  apply (cancel_epi (F.map (DerivedCategory.Q.map q))).mp
  rw [α.naturality, β.naturality, h L hL]

set_option maxHeartbeats 1000000 in
-- Elaborating the ringed sequence-site functors needs a larger local budget.
-- The normalized comparison itself makes the target coordinate invertible.
private theorem representative_coordinate_iso (P : PurityFiniteSetting.{u}) (D : Models P)
    (E F : Index P) (h : E ≤ F) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (K : CochainComplex (SpTowerShriek.S P.coefficients.l E.val Y) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients
      (R := systemRing (Scheme.ProEt.topology Y) (SpTowerShriek.B P.coefficients.l E.val Y)
        (SpTowerShriek.tau P.coefficients.l E.val Y)) K) :
    IsIso ((D.scalars E F h Z).model.ε.app
      ((((D.operations E).geometry g).pull.mapHomologicalComplex (.up ℤ)).obj K)) := by
  have : IsIso ((D.scalars E F h Y).model.ε.app K) :=
    (D.scalars E F h Y).model.computes K hK
  let a := (D.pull E F h g).derived.hom.app (DerivedCategory.Q.obj K) ≫
    (D.scalars E F h Z).T.map
      (((D.operations E).geometry g).pull.mapDerivedCategoryFactors.hom.app K)
  have : IsIso (a ≫ (D.scalars E F h Z).model.ε.app
      ((((D.operations E).geometry g).pull.mapHomologicalComplex (.up ℤ)).obj K)) := by
    dsimp only [a]
    rw [Category.assoc, representative_all P D E F h g K]
    have : IsIso
        (((D.operations F).geometry g).pull.mapDerivedCategoryFactors.hom.app
          (((D.scalars E F h Y).model.E.mapHomologicalComplex (.up ℤ)).obj K)) :=
      (Iso.app ((D.operations F).geometry g).pull.mapDerivedCategoryFactors _).isIso_hom
    have : IsIso
        ((NatTrans.mapHomologicalComplex (D.pull E F h g).ordinary.hom (.up ℤ)).app K) :=
      (Iso.app (NatIso.mapHomologicalComplex (D.pull E F h g).ordinary (.up ℤ)) K).isIso_hom
    infer_instance
  have : IsIso a := by
    dsimp only [a]
    have : IsIso (((D.operations E).geometry g).pull.mapDerivedCategoryFactors.hom.app K) :=
      (Iso.app ((D.operations E).geometry g).pull.mapDerivedCategoryFactors K).isIso_hom
    infer_instance
  exact IsIso.of_isIso_comp_left a _

set_option maxHeartbeats 2000000 in
-- The final coordinate calculation elaborates several whole-system functors.
/-- The normalized derived pullback comparison respects coefficient composition and identity.
Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), coefficient-square and composition paragraphs
(blueprint: lem-route-field-shriek-system-pullback-cocycle).

Proof:
1. On the ringed sequence sites the restriction/pushforward squares, restriction
   compositors and restriction unitors are identity on every section. Thus their two
   composite squares agree, including the identity square, as module-sheaf maps.
2. Take both adjunction mates. Mate pasting and change of adjunction identify the scalar
   boundaries with the specified ordinary scalar associator and unitor. Bijectivity of
   mating gives the ordinary pullback composition and identity equalities.
3. Extend the scalar transpose formula and PullComparison.representative from K-flat
   complexes to every complex: at a K-flat resolution q : K → P, naturality and the
   invertibility of the source image of Q(q) carry the equation from K to P. No
   K-flatness preservation by scalar extension or geometric pullback is needed. This
   gives the representative formulas for the specified scalar associator and unitor.
4. At QK, K K-flat, postcompose both sides by the target coordinate
   C_Z^{E,L}(ξ_E(K)) ≫ ε_Z^{E,L}(V_E K); it is invertible by the cochain model computation
   for ε_Y^{E,L}(K) and the E to L representative equation. Naturality and these formulas
   turn the derived composition equation into the ordinary equation of step 2.
5. For E to E use the same representative equation and the separate scalar-unit
   representative formula. In the resulting coordinates the desired unit equation is
   precisely the ordinary unit equation of step 2. Cancel the coordinates.
6. Every derived object is isomorphic to QK for such a resolution. Naturality transports
   both equalities from QK to that object; cancel the image of the resolution isomorphism.
   Objectwise equality is equality of natural transformations before finite evaluation.
-/
theorem field_shriek_system_pullback_cocycle
    (P : PurityFiniteSetting.{u}) (D : Models P)
    (E F L : Index P) (h : E ≤ F) (k : F ≤ L)
    {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (hcZ : coefficientMap P (D.coefficients E L (h.trans k)) Z =
      coefficientMap P (D.coefficients E F h) Z ≫ coefficientMap P (D.coefficients F L k) Z)
    (hcY : coefficientMap P (D.coefficients E L (h.trans k)) Y =
      coefficientMap P (D.coefficients E F h) Y ≫ coefficientMap P (D.coefficients F L k) Y)
    (hiZ : coefficientMap P (D.coefficients E E le_rfl) Z = 𝟙 _)
    (hiY : coefficientMap P (D.coefficients E E le_rfl) Y = 𝟙 _) :
    (Functor.whiskerLeft (D.scalars E F h Y).T (D.pull F L k g).derived.hom ≫
        Functor.whiskerRight (D.pull E F h g).derived.hom (D.scalars F L k Z).T ≫
        Functor.whiskerLeft
          (SpTowerShriek.pull P.coefficients.l E.val (D.base E) ((D.operations E).geometry g))
          (scalarAssoc P D h k Z hcZ).hom =
      Functor.whiskerRight (scalarAssoc P D h k Y hcY).hom
          (SpTowerShriek.pull P.coefficients.l L.val (D.base L) ((D.operations L).geometry g)) ≫
        (D.pull E L (h.trans k) g).derived.hom) ∧
    ((D.pull E E le_rfl g).derived.hom ≫
        Functor.whiskerLeft
          (SpTowerShriek.pull P.coefficients.l E.val (D.base E) ((D.operations E).geometry g))
          (scalarUnit P D E Z hiZ).hom =
      Functor.whiskerRight (scalarUnit P D E Y hiY).hom
        (SpTowerShriek.pull P.coefficients.l E.val (D.base E) ((D.operations E).geometry g))) := by
  constructor
  · apply derived_ext_kflat P E Y
    intro K hK
    have := representative_coordinate_iso P D E L (h.trans k) g K hK
    apply (Iso.cancel_iso_hom_right _ _
      ((D.scalars E L (h.trans k) Z).T.mapIso
          (Iso.app ((D.operations E).geometry g).pull.mapDerivedCategoryFactors K) ≪≫
        asIso ((D.scalars E L (h.trans k) Z).model.ε.app
          ((((D.operations E).geometry g).pull.mapHomologicalComplex (.up ℤ)).obj K)))).mp
    have he := composition_coordinates
      DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
      DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
      ((D.scalars E F h Y).model.E.mapHomologicalComplex (.up ℤ))
      ((D.scalars F L k Y).model.E.mapHomologicalComplex (.up ℤ))
      ((D.scalars E L (h.trans k) Y).model.E.mapHomologicalComplex (.up ℤ))
      ((D.scalars E F h Z).model.E.mapHomologicalComplex (.up ℤ))
      ((D.scalars F L k Z).model.E.mapHomologicalComplex (.up ℤ))
      ((D.scalars E L (h.trans k) Z).model.E.mapHomologicalComplex (.up ℤ))
      (((D.operations E).geometry g).pull.mapHomologicalComplex (.up ℤ))
      (((D.operations F).geometry g).pull.mapHomologicalComplex (.up ℤ))
      (((D.operations L).geometry g).pull.mapHomologicalComplex (.up ℤ))
      (D.scalars E F h Y).T (D.scalars F L k Y).T (D.scalars E L (h.trans k) Y).T
      (D.scalars E F h Z).T (D.scalars F L k Z).T (D.scalars E L (h.trans k) Z).T
      (SpTowerShriek.pull P.coefficients.l E.val (D.base E) ((D.operations E).geometry g))
      (SpTowerShriek.pull P.coefficients.l F.val (D.base F) ((D.operations F).geometry g))
      (SpTowerShriek.pull P.coefficients.l L.val (D.base L) ((D.operations L).geometry g))
      (D.scalars E F h Y).model.ε (D.scalars F L k Y).model.ε
      (D.scalars E L (h.trans k) Y).model.ε
      (D.scalars E F h Z).model.ε (D.scalars F L k Z).model.ε
      (D.scalars E L (h.trans k) Z).model.ε
      ((D.operations E).geometry g).pull.mapDerivedCategoryFactors.hom
      ((D.operations F).geometry g).pull.mapDerivedCategoryFactors.hom
      ((D.operations L).geometry g).pull.mapDerivedCategoryFactors.hom
      (D.pull E F h g).derived.hom (D.pull F L k g).derived.hom
      (D.pull E L (h.trans k) g).derived.hom
      (NatTrans.mapHomologicalComplex (D.pull E F h g).ordinary.hom (.up ℤ))
      (NatTrans.mapHomologicalComplex (D.pull F L k g).ordinary.hom (.up ℤ))
      (NatTrans.mapHomologicalComplex (D.pull E L (h.trans k) g).ordinary.hom (.up ℤ))
      (scalarAssoc P D h k Y hcY).hom (scalarAssoc P D h k Z hcZ).hom
      (NatTrans.mapHomologicalComplex (ordinaryAssoc P D h k Y hcY).hom (.up ℤ))
      (NatTrans.mapHomologicalComplex (ordinaryAssoc P D h k Z hcZ).hom (.up ℤ))
      (representative_all P D E F h g) (representative_all P D F L k g)
      (representative_all P D E L (h.trans k) g)
      (scalarAssoc_rep P D h k Y hcY) (scalarAssoc_rep P D h k Z hcZ)
      (by
        intro M
        apply HomologicalComplex.hom_ext
        intro n
        exact congr_app (ordinary_composition P D E F L h k g hcZ hcY) (M.X n)) K
    simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, asIso_hom, Functor.comp_obj, Category.assoc] using he
  · apply derived_ext_kflat P E Y
    intro K _
    apply (Iso.cancel_iso_hom_right _ _
      (Iso.app ((D.operations E).geometry g).pull.mapDerivedCategoryFactors K)).mp
    have he := unit_coordinates DerivedCategory.Q DerivedCategory.Q
      ((D.scalars E E le_rfl Y).model.E.mapHomologicalComplex (.up ℤ))
      ((D.scalars E E le_rfl Z).model.E.mapHomologicalComplex (.up ℤ))
      (((D.operations E).geometry g).pull.mapHomologicalComplex (.up ℤ))
      (D.scalars E E le_rfl Y).T (D.scalars E E le_rfl Z).T
      (SpTowerShriek.pull P.coefficients.l E.val (D.base E) ((D.operations E).geometry g))
      (D.scalars E E le_rfl Y).model.ε (D.scalars E E le_rfl Z).model.ε
      ((D.operations E).geometry g).pull.mapDerivedCategoryFactors.hom
      (D.pull E E le_rfl g).derived.hom
      (NatTrans.mapHomologicalComplex (D.pull E E le_rfl g).ordinary.hom (.up ℤ))
      (scalarUnit P D E Y hiY).hom (scalarUnit P D E Z hiZ).hom
      (NatTrans.mapHomologicalComplex (ordinaryUnit P D E Y hiY).hom (.up ℤ))
      (NatTrans.mapHomologicalComplex (ordinaryUnit P D E Z hiZ).hom (.up ℤ))
      (representative_all P D E E le_rfl g)
      (scalarUnit_rep P D E Y hiY) (scalarUnit_rep P D E Z hiZ)
      (by
        intro M
        apply HomologicalComplex.hom_ext
        intro n
        exact congr_app (ordinary_identity P D E g hiZ hiY) (M.X n)) K
    simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Iso.app_hom,
      Functor.comp_obj, Category.assoc] using he

end AlgebraicGeometry.ProEtale.FieldShriekSystem
