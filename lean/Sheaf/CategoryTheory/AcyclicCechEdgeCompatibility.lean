/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SiteCechEdgeNormalization
public import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
public import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteInjectiveCechAcyclic
import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic

import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Sheaf.Algebra.Homology.FirstQuadrantAugmentation
import Sheaf.CategoryTheory.SitePullbackAbelianExact
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Canonical acyclic Čech edges and their compatibility

Source: Stacks Project, Cohomology on Sites, Tags 03AX, 03AZ, 03F7, 03FD
(blueprint: lem-weil-pbc-acyclic-cech-edge-compatibility).

Cohomology is expressed by right derived evaluation, as in the source's definition.
The existing cohomology-over-object comparison identifies it with `Sheaf.H'`.
Module cohomology is computed in the module category before forgetting scalars.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

-- The upstream theorem supplies the instance on every small ringed site.
attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace SiteCechComplex

section Comparison

variable {C : Type u} [SmallCategory C] {T : Type u} {U : C}
  {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom)
  {E : Type*} [Category E] [Abelian E] [EnoughInjectives E]
  (P : E ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u}) [P.Additive]

omit [EnoughInjectives E] in
private theorem augmentations_alpha_eq {A : E} (I : InjectiveResolution A)
    (d d' : S.Augmentations P I) : d.alpha = d'.alpha := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [d.alpha_f, d'.alpha_f]

omit [EnoughInjectives E] in
private theorem augmentations_beta_eq {A : E} (I : InjectiveResolution A)
    (d d' : S.Augmentations P I) : d.beta = d'.beta := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [d.beta_f, d'.beta_f]

private noncomputable def totalResolutionMap {A B : E}
    (I : InjectiveResolution A) (L : InjectiveResolution B)
    (v : I.cocomplex ⟶ L.cocomplex) :
    (S.resolutionDoubleComplex P I).total (.up ℕ) ⟶
      (S.resolutionDoubleComplex P L).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ _ _).map
      (((P ⋙ S.complexFunctor).mapHomologicalComplex (.up ℕ)).map v)) (.up ℕ)

omit [EnoughInjectives E] in
set_option backward.isDefEq.respectTransparency false in
private theorem alpha_naturality {A B : E}
    (I : InjectiveResolution A) (L : InjectiveResolution B)
    (d : S.Augmentations P I) (d' : S.Augmentations P L)
    (v : I.cocomplex ⟶ L.cocomplex) :
    ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
      (.up ℕ)).map v ≫ d'.alpha =
        d.alpha ≫ S.totalResolutionMap P I L v := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, d.alpha_f, d'.alpha_f, Category.assoc,
    totalResolutionMap, HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply AddCommGrpCat.ext
  intro s
  funext t
  exact congrArg (fun k ↦ k s)
    ((P.map (v.f n)).naturality (S.pr 0 t 0 ≫ hom (t 0)).op).symm

omit [EnoughInjectives E] in
set_option backward.isDefEq.respectTransparency false in
private theorem beta_naturality {A B : E} (g : A ⟶ B)
    (I : InjectiveResolution A) (L : InjectiveResolution B)
    (d : S.Augmentations P I) (d' : S.Augmentations P L)
    (v : I.cocomplex ⟶ L.cocomplex)
    (hv : I.ι.f 0 ≫ v.f 0 = g ≫ L.ι.f 0) :
    S.complexMap (P.map g) ≫ d'.beta =
      d.beta ≫ S.totalResolutionMap P I L v := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, d.beta_f, d'.beta_f, Category.assoc,
    totalResolutionMap, HomologicalComplex₂.ιTotal_map]
  have h := congrArg (fun k ↦ ((P ⋙ S.complexFunctor).map k).f n) hv
  have hh := congrArg (fun k ↦ k ≫
    (S.resolutionDoubleComplex P L).ιTotal (.up ℕ) n 0 n (by simp)) h.symm
  simp only [Functor.map_comp, HomologicalComplex.comp_f, Category.assoc] at hh
  exact hh

private def restriction (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    F.obj (op U) ⟶ S.cochains F 0 :=
  AddCommGrpCat.ofHom (AddMonoidHom.pi fun t : Fin (0 + 1) → T ↦
    (F.map (S.pr 0 t 0 ≫ hom (t 0)).op).hom)

private theorem restriction_d (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    S.restriction F ≫ (S.complex F).d 0 1 = 0 := by
  apply AddCommGrpCat.ext
  intro x
  funext t
  have h (k : Fin 2) : F.map (S.indexMap t k.succAbove).op
      (F.map (S.pr 0 (t ∘ k.succAbove) 0 ≫ hom (t (k.succAbove 0))).op x) =
      F.map (S.pr 1 t 0 ≫ hom (t 0)).op x := by
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp]
    rw [← Category.assoc, S.indexMap_pr, S.comm]
  change (∑ k : Fin 2, (-1 : ℤ) ^ k.val •
    F.map (S.indexMap t k.succAbove).op
      (F.map (S.pr 0 (t ∘ k.succAbove) 0 ≫ hom (t (k.succAbove 0))).op x)) = 0
  simp only [Fin.sum_univ_two, h, Fin.val_zero, pow_zero, one_smul,
    Fin.val_one, pow_one, neg_smul, add_neg_cancel]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def restrictionToZero {A : E} (I : InjectiveResolution A) :
    ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex ⟶ (S.resolutionDoubleComplex P I).X 0 where
  f q := S.restriction (P.obj (I.cocomplex.X q))
  comm' q r _ := by
    apply AddCommGrpCat.ext
    intro x
    funext t
    exact congrArg (fun k ↦ k x)
      ((P.map (I.cocomplex.d q r)).naturality (S.pr 0 t 0 ≫ hom (t 0)).op)

omit [EnoughInjectives E] in
private theorem restrictionToZero_d {A : E} (I : InjectiveResolution A) :
    S.restrictionToZero P I ≫ (S.resolutionDoubleComplex P I).d 0 1 = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  exact S.restriction_d (P.obj (I.cocomplex.X n))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def alpha {A : E} (I : InjectiveResolution A) :
    ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex ⟶ (S.resolutionDoubleComplex P I).total (.up ℕ) where
  f q := (S.restrictionToZero P I).f q ≫
    (S.resolutionDoubleComplex P I).ιTotal (.up ℕ) 0 q q (by simp)
  comm' q r h := by
    have hr : q + 1 = r := h
    subst r
    let D := S.resolutionDoubleComplex P I
    let a := S.restrictionToZero P I
    simp only [HomologicalComplex₂.total_d, Category.assoc,
      Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel 0 1)
      q (q + 1) (by simp [Nat.add_comm]),
      D.d₂_eq (.up ℕ) 0 (by simp : (ComplexShape.up ℕ).Rel q (q + 1)) (q + 1) (by simp)]
    have hz := congrArg (fun k ↦ k.f q) (S.restrictionToZero_d P I)
    change (S.restrictionToZero P I).f q ≫ (D.d 0 1).f q = 0 at hz
    have hs₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := rfl
    have hs₂ : ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := by
      change (-1 : ℤˣ) ^ 0 = 1
      exact pow_zero _
    simp only [hs₁, hs₂, one_smul, ← Category.assoc, hz, zero_comp, zero_add]
    rw [a.comm q (q + 1)]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def beta {A : E} (I : InjectiveResolution A) :
    S.complex (P.obj A) ⟶ (S.resolutionDoubleComplex P I).total (.up ℕ) where
  f p := S.cochainsMap (P.map (I.ι.f 0)) p ≫
    (S.resolutionDoubleComplex P I).ιTotal (.up ℕ) p 0 p (by simp)
  comm' p r h := by
    have hr : p + 1 = r := h
    subst r
    let D := S.resolutionDoubleComplex P I
    let a := (P ⋙ S.complexFunctor).map (I.ι.f 0)
    have hz : a ≫ (P ⋙ S.complexFunctor).map (I.cocomplex.d 0 1) = 0 := by
      rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero]
    have hz' := congrArg (fun k ↦ k.f p) hz
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz'
    simp only [HomologicalComplex₂.total_d, Category.assoc,
      Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel p (p + 1))
      0 (p + 1) (by simp),
      D.d₂_eq (.up ℕ) p (by simp : (ComplexShape.up ℕ).Rel 0 1) (p + 1) (by simp)]
    have hs₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (p, 0) = 1 := rfl
    simp only [hs₁, one_smul]
    change a.f p ≫ (D.d p (p + 1)).f 0 ≫ D.ιTotal (.up ℕ) (p + 1) 0 (p + 1) _ +
      a.f p ≫ (_ • (D.X p).d 0 1 ≫ D.ιTotal (.up ℕ) p 1 (p + 1) _) = _
    simp only [← Category.assoc]
    have hz'' : a.f p ≫
        (ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (p, 0) •
          ((D.X p).d 0 1 ≫ D.ιTotal (.up ℕ) p 1 (p + 1) (by simp))) = 0 := by
      rw [Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc]
      change _ • ((a.f p ≫ ((P ⋙ S.complexFunctor).map
        (I.cocomplex.d 0 1)).f p) ≫ _) = 0
      rw [hz', zero_comp, smul_zero]
    rw [hz'', add_zero]
    exact congrArg (fun k ↦ k ≫ D.ιTotal (.up ℕ) (p + 1) 0 (p + 1) (by simp))
      (a.comm p (p + 1))

private noncomputable def augmentations {A : E} (I : InjectiveResolution A) :
    S.Augmentations P I where
  alpha := S.alpha P I
  beta := S.beta P I
  alpha_f _ := rfl
  beta_f _ := rfl

private noncomputable def edgeFromResolution {A : E} (I : InjectiveResolution A)
    [QuasiIso (S.alpha P I)] (q : ℕ) :
    (S.cohomologyFunctor q).obj (P.obj A) ⟶
      ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj A :=
  HomologicalComplex.homologyMap (S.beta P I) q ≫
    inv (HomologicalComplex.homologyMap (S.alpha P I) q) ≫
      (I.isoRightDerivedObj (P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).inv

private theorem edgeFromResolution_spec {A : E} (I : InjectiveResolution A)
    [QuasiIso (S.alpha P I)] (q : ℕ) :
    S.edgeFromResolution P I q ≫ (I.isoRightDerivedObj
      (P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom ≫
        HomologicalComplex.homologyMap (S.alpha P I) q =
          HomologicalComplex.homologyMap (S.beta P I) q := by
  simp [edgeFromResolution, Category.assoc]

private theorem normalizedEdge_unique {A : E} (q : ℕ)
    (e e' : (S.cohomologyFunctor q).obj (P.obj A) ⟶
      ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj A)
    (he : S.IsNormalizedEdge P q e) (he' : S.IsNormalizedEdge P q e') : e = e' := by
  let I := injectiveResolution A
  obtain ⟨d, hd, he⟩ := he I
  obtain ⟨d', _, he'⟩ := he' I
  have := hd
  rw [← S.augmentations_alpha_eq P I d d', ← S.augmentations_beta_eq P I d d'] at he'
  exact (cancel_mono ((I.isoRightDerivedObj
    (P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom ≫
      HomologicalComplex.homologyMap d.alpha q)).mp (he.trans he'.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem resolutionEdge_naturality {A B : E} (g : A ⟶ B) (q : ℕ)
    (I : InjectiveResolution A) (L : InjectiveResolution B)
    (d : S.Augmentations P I) (d' : S.Augmentations P L)
    (v : I.cocomplex ⟶ L.cocomplex)
    (hv : I.ι.f 0 ≫ v.f 0 = g ≫ L.ι.f 0)
    (e : (S.cohomologyFunctor q).obj (P.obj A) ⟶
      ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj A)
    (e' : (S.cohomologyFunctor q).obj (P.obj B) ⟶
      ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj B)
    (hd' : QuasiIso d'.alpha)
    (he : e ≫ (I.isoRightDerivedObj
      (P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom ≫
        HomologicalComplex.homologyMap d.alpha q = HomologicalComplex.homologyMap d.beta q)
    (he' : e' ≫ (L.isoRightDerivedObj
      (P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom ≫
        HomologicalComplex.homologyMap d'.alpha q = HomologicalComplex.homologyMap d'.beta q) :
    (S.cohomologyFunctor q).map (P.map g) ≫ e' =
      e ≫ ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).map g := by
  have := hd'
  let F := P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)
  apply (cancel_mono ((L.isoRightDerivedObj F q).hom ≫
    HomologicalComplex.homologyMap d'.alpha q)).mp
  have hα := congrArg (fun k ↦ HomologicalComplex.homologyMap k q)
    (S.alpha_naturality P I L d d' v)
  have hβ := congrArg (fun k ↦ HomologicalComplex.homologyMap k q)
    (S.beta_naturality P g I L d d' v hv)
  simp only [HomologicalComplex.homologyMap_comp] at hα hβ
  have hn := InjectiveResolution.isoRightDerivedObj_hom_naturality g I L v hv F q
  change (S.cohomologyFunctor q).map (P.map g) ≫ e' ≫
    (L.isoRightDerivedObj F q).hom ≫ HomologicalComplex.homologyMap d'.alpha q =
      (e ≫ (F.rightDerived q).map g) ≫
        (L.isoRightDerivedObj F q).hom ≫ HomologicalComplex.homologyMap d'.alpha q
  simp only [Category.assoc] at he he' ⊢
  rw [he']
  change HomologicalComplex.homologyMap (S.complexMap (P.map g)) q ≫
    HomologicalComplex.homologyMap d'.beta q = _
  rw [hβ, ← he]
  simp only [Category.assoc]
  rw [← hα]
  change (F.rightDerived q).map g ≫ (L.isoRightDerivedObj F q).hom =
    (I.isoRightDerivedObj F q).hom ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map v) q at hn
  simpa only [Category.assoc] using
    congrArg (fun k ↦ e ≫ k ≫ HomologicalComplex.homologyMap d'.alpha q) hn.symm

set_option backward.isDefEq.respectTransparency false in
private theorem normalizedEdge_naturality {A B : E} (g : A ⟶ B) (q : ℕ)
    (e : (S.cohomologyFunctor q).obj (P.obj A) ⟶
      ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj A)
    (e' : (S.cohomologyFunctor q).obj (P.obj B) ⟶
      ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj B)
    (he : S.IsNormalizedEdge P q e) (he' : S.IsNormalizedEdge P q e') :
    (S.cohomologyFunctor q).map (P.map g) ≫ e' =
      e ≫ ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).map g := by
  let I := injectiveResolution A
  let L := injectiveResolution B
  let v := InjectiveResolution.desc g L I
  have hv : I.ι.f 0 ≫ v.f 0 = g ≫ L.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero g L I
  obtain ⟨d, hd, he⟩ := he I
  obtain ⟨d', hd', he'⟩ := he' L
  exact S.resolutionEdge_naturality P g q I L d d' v hv e e' hd' he he'

end Comparison

end SiteCechComplex

private theorem edge_comparison_square
    {E : Type*} [Category* E] {A B C D A' B' C' D' : E}
    (ρ : B ≅ C) (σ : B' ≅ C')
    {α : C ⟶ D} {α' : C' ⟶ D'} [hα'iso : IsIso α']
    {β : A ⟶ D} {β' : A' ⟶ D'} {e : A ⟶ B} {e' : A' ⟶ B'}
    {w : C ⟶ C'} {V : D ⟶ D'} {h : A ⟶ A'}
    (hα : α ≫ V = w ≫ α') (hβ : h ≫ β' = β ≫ V)
    (he : e ≫ ρ.hom ≫ α = β) (he' : e' ≫ σ.hom ≫ α' = β') :
    e ≫ ρ.hom ≫ w ≫ σ.inv = h ≫ e' := by
  apply (cancel_mono (σ.hom ≫ α')).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← hα]
  calc
    e ≫ ρ.hom ≫ α ≫ V = β ≫ V := by rw [← he]; simp only [Category.assoc]
    _ = h ≫ β' := hβ.symm
    _ = h ≫ e' ≫ σ.hom ≫ α' := by rw [he']

private theorem resolution_formula_from_square
    {E : Type*} [Category* E] {X Y Z V : E} (ρ : X ≅ Y)
    {e : Z ⟶ X} {a : Z ⟶ V} {b : V ⟶ Y} (h : e ≫ ρ.hom = a ≫ b) :
    e = a ≫ b ≫ ρ.inv := by
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv ρ).mpr h

private theorem transport_edge_normalization
    {E : Type*} [Category* E] {A B C D B' C' D' : E}
    (c : B ≅ B') (ρ : B ≅ C) (σ : B' ≅ C')
    {α : C ⟶ D} {α' : C' ⟶ D'} [hαiso : IsIso α] [hα'iso : IsIso α']
    {β : A ⟶ D} {β' : A ⟶ D'} {e : A ⟶ B'}
    {w : C ⟶ C'} {V : D ⟶ D'}
    (hα : α ≫ V = w ≫ α') (hβ : β ≫ V = β')
    (hc : c.hom ≫ σ.hom = ρ.hom ≫ w) (he : e ≫ σ.hom ≫ α' = β') :
    (e ≫ c.inv) ≫ ρ.hom ≫ α = β := by
  have hw : IsIso w := by
    have : IsIso (ρ.hom ≫ w) := by rw [← hc]; infer_instance
    exact IsIso.of_isIso_comp_left ρ.hom w
  have hV : IsIso V := by
    have : IsIso (α ≫ V) := by rw [hα]; infer_instance
    exact IsIso.of_isIso_comp_left α V
  apply (cancel_mono V).mp
  simp only [Category.assoc]
  rw [hα, ← Category.assoc ρ.hom w α', ← hc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact he.trans hβ.symm

private theorem universal_derived_comparison
    {E D : Type*} [Category* E] [Abelian E] [EnoughInjectives E]
    [Category* D] [Abelian D]
    (v : E ⥤ D) [v.Additive] [PreservesFiniteLimits v]
    (w : ℕ → E ⥤ D) (c : ∀ q : ℕ, v.rightDerived q ≅ w q) :
    ∃ (G H : CohomologicalDeltaFunctor E D)
      (g : ∀ q : ℕ, G.F q ≅ v.rightDerived q)
      (h : ∀ q : ℕ, H.F q ≅ w q),
      G.IsUniversal ∧ H.IsUniversal ∧
        ∃ t : CohomologicalDeltaFunctor.Hom G H,
          (∀ q : ℕ, (g q).inv ≫ t.app q ≫ (h q).hom = (c q).hom) ∧
          ∀ t' : CohomologicalDeltaFunctor.Hom G H,
            (g 0).inv ≫ t'.app 0 ≫ (h 0).hom = (c 0).hom → t' = t := by
  obtain ⟨G, hG, hGu, _⟩ := v.exists_universal_rightDerived_deltaFunctor
  let g (q : ℕ) : G.F q ≅ v.rightDerived q := eqToIso (congrFun hG q)
  let h (q : ℕ) : G.F q ≅ w q := g q ≪≫ c q
  let t : CohomologicalDeltaFunctor.Hom G G :=
    ⟨fun _ ↦ 𝟙 _, by intros; simp⟩
  refine ⟨G, G, g, h, hGu, hGu, t, ?_, ?_⟩
  · intro q
    simp [h, t]
  · intro t' ht'
    have ht0 : t'.app 0 = 𝟙 (G.F 0) := by
      apply (cancel_epi (g 0).inv).mp
      apply (cancel_mono (h 0).hom).mp
      simpa [h, Category.assoc] using ht'
    obtain ⟨t0, _, huniq⟩ := hGu G (𝟙 (G.F 0))
    exact (huniq t' ht0).trans (huniq t rfl).symm

private theorem exact_resolution_lift
    {E D : Type*} [Category* E] [Abelian E] [Category* D] [Abelian D]
    (F : E ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A : E} {B : D} (I : InjectiveResolution A) (L : InjectiveResolution B)
    (g : F.obj A ⟶ B) :
    ∃ k : (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ L.cocomplex,
      F.map (I.ι.f 0) ≫ k.f 0 = g ≫ L.ι.f 0 := by
  let a := (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app A ≫
    (F.mapHomologicalComplex (.up ℕ)).map I.ι
  have ha : QuasiIso a := by dsimp [a]; infer_instance
  let k := InjectiveResolution.descOfQuasiIso g L a
  refine ⟨k, ?_⟩
  have hh := InjectiveResolution.comp_descOfQuasiIsoFZero g L a
  change a.f 0 ≫ k.f 0 = g ≫ L.ι.f 0 at hh
  simp only [a, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp] at hh
  change (F.map (𝟙 A) ≫ F.map (I.ι.f 0)) ≫ k.f 0 = g ≫ L.ι.f 0 at hh
  simpa only [Functor.map_id, Category.id_comp] using hh

private theorem adjunction_resolution_lift
    {E D : Type*} [Category* E] [Abelian E] [Category* D] [Abelian D]
    (F : E ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    {A : E} {B : D} (I : InjectiveResolution A) (L : InjectiveResolution B)
    (h : A ⟶ G.obj B) :
    ∃ v : I.cocomplex ⟶ (G.mapHomologicalComplex (.up ℕ)).obj L.cocomplex,
      I.ι.f 0 ≫ v.f 0 = h ≫ G.map (L.ι.f 0) := by
  obtain ⟨j, hj⟩ := exact_resolution_lift F I L ((adj.homEquiv A B).symm h)
  let v : I.cocomplex ⟶ (G.mapHomologicalComplex (.up ℕ)).obj L.cocomplex :=
    { f := fun n ↦ adj.unit.app (I.cocomplex.X n) ≫ G.map (j.f n)
      comm' := by
        intro m n _
        change (adj.unit.app (I.cocomplex.X m) ≫ G.map (j.f m)) ≫
          G.map (L.cocomplex.d m n) = I.cocomplex.d m n ≫
            adj.unit.app (I.cocomplex.X n) ≫ G.map (j.f n)
        symm
        have hη : I.cocomplex.d m n ≫ adj.unit.app (I.cocomplex.X n) =
            adj.unit.app (I.cocomplex.X m) ≫ G.map (F.map (I.cocomplex.d m n)) := by
          simpa only [Functor.id_map, Functor.comp_map] using
            adj.unit.naturality (I.cocomplex.d m n)
        have hjc : F.map (I.cocomplex.d m n) ≫ j.f n =
            j.f m ≫ L.cocomplex.d m n := (j.comm m n).symm
        rw [← Category.assoc, hη, Category.assoc, ← G.map_comp, hjc,
          G.map_comp, Category.assoc] }
  refine ⟨v, ?_⟩
  change I.ι.f 0 ≫ adj.unit.app (I.cocomplex.X 0) ≫ G.map (j.f 0) = _
  have hn : I.ι.f 0 ≫ adj.unit.app (I.cocomplex.X 0) =
      adj.unit.app A ≫ G.map (F.map (I.ι.f 0)) :=
    adj.unit.naturality (I.ι.f 0)
  rw [← Category.assoc, hn, Category.assoc, ← G.map_comp, hj, G.map_comp]
  have hh := (adj.homEquiv A B).apply_symm_apply h
  rw [adj.homEquiv_unit] at hh
  rw [← Category.assoc, hh]

private theorem cech_zero_glue
    {C : Type u} [SmallCategory C]
    {J : Precoverage C} [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type u} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (c : S.cochains I.obj 0) (hc : S.differentialValue I.obj 0 c = 0) :
    ∃! x : I.obj.obj (op U), ∀ t, I.obj.map
      (S.pr 0 t 0 ≫ hom (t 0)).op x = c t := by
  classical
  let P := I.obj ⋙ forget AddCommGrpCat
  have hs : Presieve.IsSheaf J.toGrothendieck P :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ I.obj (forget AddCommGrpCat) I.property)
  have hg := (Presieve.isSheafFor_arrows_iff P hom).mp
    (hs.isSheafFor_of_mem_precoverage hcover)
  let a (i : T) := I.obj.map (eqToHom (S.W_zero (fun _ ↦ i)).symm).op (c (fun _ ↦ i))
  have transport (t : Fin 1 → T) (i : T) (ht : t = fun _ ↦ i)
      (Z : C) (g : Z ⟶ f i) :
      I.obj.map (g ≫ eqToHom (by simpa only [ht] using (S.W_zero t).symm)).op
        (c t) = I.obj.map g.op (a i) := by
    subst t
    rw [op_comp, I.obj.map_comp]
    rfl
  have ha : Presieve.Arrows.Compatible P hom a := by
    intro i j Z gi gj hij
    let t : Fin 2 → T := Fin.cons i (fun _ ↦ j)
    let g : ∀ k : Fin 2, Z ⟶ f (t k) := Fin.cases gi (fun _ ↦ gj)
    obtain ⟨b, hb, _⟩ := S.universal 1 t Z g (by
      intro k
      fin_cases k
      · rfl
      · exact hij.symm)
    have he := congrArg (fun s ↦ I.obj.map b.op (s t)) hc
    change I.obj.map b.op (∑ k : Fin 2, (-1 : ℤ) ^ k.val •
      I.obj.map (S.indexMap t k.succAbove).op (c (t ∘ k.succAbove))) =
        I.obj.map b.op 0 at he
    simp only [Fin.sum_univ_two,
      Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      map_add, map_neg, map_zero] at he
    have ht0 : t ∘ (0 : Fin 2).succAbove = (fun _ ↦ j) := by
      funext k
      fin_cases k
      rfl
    have ht1 : t ∘ (1 : Fin 2).succAbove = (fun _ ↦ i) := by
      funext k
      fin_cases k
      rfl
    have hm (k : Fin 2) : b ≫ S.indexMap t k.succAbove =
        g (k.succAbove 0) ≫
          eqToHom (S.W_zero (t ∘ k.succAbove)).symm := by
      have : IsIso (S.pr 0 (t ∘ k.succAbove) 0) := by
        rw [S.pr_zero]
        infer_instance
      apply (cancel_mono (S.pr 0 (t ∘ k.succAbove) 0)).mp
      rw [Category.assoc, S.indexMap_pr, hb, Category.assoc, S.pr_zero]
      simp
    simp only [← ConcreteCategory.comp_apply, ← I.obj.map_comp, ← op_comp, hm] at he
    change I.obj.map (gj ≫ eqToHom (S.W_zero (t ∘ (0 : Fin 2).succAbove)).symm).op
      (c (t ∘ (0 : Fin 2).succAbove)) +
      -I.obj.map (gi ≫ eqToHom (S.W_zero (t ∘ (1 : Fin 2).succAbove)).symm).op
        (c (t ∘ (1 : Fin 2).succAbove)) = 0 at he
    rw [transport _ j ht0 Z gj, transport _ i ht1 Z gi] at he
    exact (add_neg_eq_zero.mp he).symm
  obtain ⟨x, hx, hu⟩ := hg a ha
  have hx' : ∀ t, I.obj.map (S.pr 0 t 0 ≫ hom (t 0)).op x = c t := by
    intro t
    obtain ⟨i, rfl⟩ : ∃ i, t = (fun _ : Fin 1 ↦ i) := ⟨t 0, by
      funext k
      fin_cases k
      rfl⟩
    have he := congrArg (fun y ↦ I.obj.map (S.pr 0 (fun _ ↦ i) 0).op y) (hx i)
    dsimp [P, a] at he
    rw [← ConcreteCategory.comp_apply, ← I.obj.map_comp] at he
    rw [← ConcreteCategory.comp_apply, ← I.obj.map_comp] at he
    simp only [← op_comp, S.pr_zero, eqToHom_trans, eqToHom_refl] at he
    simp only [op_id, I.obj.map_id, ConcreteCategory.id_apply] at he
    simpa only [S.pr_zero] using he
  refine ⟨x, hx', ?_⟩
  intro y hy
  apply hu y
  intro i
  have he := congrArg
    (fun z ↦ I.obj.map (eqToHom (S.W_zero (fun _ : Fin 1 ↦ i)).symm).op z)
    (hy (fun _ ↦ i))
  dsimp [P, a] at he ⊢
  change I.obj.map (eqToHom (S.W_zero (fun _ ↦ i)).symm).op
    (I.obj.map (S.pr 0 (fun _ ↦ i) 0 ≫ hom i).op y) = _ at he
  rw [← ConcreteCategory.comp_apply, ← I.obj.map_comp] at he
  simp only [← op_comp, S.pr_zero, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
private theorem site_row_augmentation_quasiIso
    {C : Type u} [SmallCategory C] {J : Precoverage C}
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (A : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (hpos : ∀ r : ℕ, 0 < r → IsZero ((S.cohomologyFunctor r).obj A.obj))
    (e : (CochainComplex.single₀ AddCommGrpCat.{u}).obj (A.obj.obj (op U)) ⟶
      S.complex A.obj) (he : e.f 0 = S.restriction A.obj) : QuasiIso e := by
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | succ n =>
    rw [quasiIsoAt_iff_exactAt e (n + 1)
      (CochainComplex.exactAt_succ_single_obj _ n)]
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hpos (n + 1) (by omega)
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    rw [ShortComplex.quasiIso_iff_isIso_liftCycles _ (by simp) (by simp) (by simp)]
    let L := S.complex A.obj
    let Q := L.sc' 0 0 1
    have hw : e.f 0 ≫ L.d 0 1 = 0 := by
      rw [e.comm]
      simp
    let k := Q.liftCycles (e.f 0) hw
    change IsIso k
    have hinj : Function.Injective k := by
      intro x y hxy
      have hres : ∀ t, A.obj.map (S.pr 0 t 0 ≫ hom (t 0)).op x =
          A.obj.map (S.pr 0 t 0 ≫ hom (t 0)).op y := by
        intro t
        have h := congrArg (fun z ↦ Q.iCycles z t) hxy
        change (k ≫ Q.iCycles) x t = (k ≫ Q.iCycles) y t at h
        rw [Q.liftCycles_i, he] at h
        exact h
      have hc : S.differentialValue A.obj 0
          (fun t ↦ A.obj.map (S.pr 0 t 0 ≫ hom (t 0)).op x) = 0 := by
        exact ConcreteCategory.congr_hom (S.restriction_d A.obj) x
      obtain ⟨z, _, hu⟩ := cech_zero_glue f hom hcover S A _ hc
      exact (hu x (fun _ ↦ rfl)).trans (hu y (fun t ↦ (hres t).symm)).symm
    have hsurj : Function.Surjective k := by
      intro y
      let c := Q.iCycles y
      have hc : S.differentialValue A.obj 0 c = 0 := by
        exact ConcreteCategory.congr_hom Q.iCycles_g y
      obtain ⟨x, hx, _⟩ := cech_zero_glue f hom hcover S A c hc
      refine ⟨x, ?_⟩
      apply (AddCommGrpCat.mono_iff_injective Q.iCycles).mp inferInstance
      change (k ≫ Q.iCycles) x = _
      rw [Q.liftCycles_i, he]
      exact funext hx
    exact (ConcreteCategory.isIso_iff_bijective k).mpr ⟨hinj, hsurj⟩

set_option backward.isDefEq.respectTransparency false in
private theorem site_alpha_quasiIso
    {C : Type u} [SmallCategory C] {J : Precoverage C}
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    {A : Sheaf J.toGrothendieck AddCommGrpCat.{u}} (I : InjectiveResolution A) :
    QuasiIso (S.alpha (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) I) := by
  let P := sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}
  apply HomologicalComplex₂.quasiIso_of_column_augmentation
    (S.resolutionDoubleComplex P I) _ (S.restrictionToZero P I)
    (S.restrictionToZero_d P I) (S.alpha P I) (fun _ ↦ rfl)
  intro n
  exact site_row_augmentation_quasiIso hcover S (I.cocomplex.X n)
    (site_injective_cech_acyclic f hom hcover S (I.cocomplex.X n)).1 _
    (CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem site_beta_column_quasiIso
    {C : Type u} [SmallCategory C] {J : Precoverage C}
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (hA : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
      IsZero (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))).rightDerived r).obj A))
    (I : InjectiveResolution A) (p : ℕ)
    (e : (CochainComplex.single₀ AddCommGrpCat.{u}).obj (S.cochains A.obj p) ⟶
      (S.resolutionDoubleComplex (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) I).X p)
    (he : e.f 0 = S.cochainsMap (sheafToPresheaf _ _ |>.map (I.ι.f 0)) p) :
    QuasiIso e := by
  let P := sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}
  let D := S.resolutionDoubleComplex P I
  let F (t : Fin (p + 1) → T) := P ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))
  let K (t : Fin (p + 1) → T) := ((F t).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hz (t : Fin (p + 1) → T) (r : ℕ) (hr : 0 < r) : (K t).ExactAt r := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hA p t r hr).of_iso (I.isoRightDerivedObj (F t) r).symm
  refine ⟨fun r ↦ ?_⟩
  cases r with
  | succ r =>
    rw [quasiIsoAt_iff_exactAt e (r + 1)
      (CochainComplex.exactAt_succ_single_obj _ r)]
    rw [HomologicalComplex.exactAt_iff' _ r (r + 1) (r + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    intro c hc
    have hlift (t : Fin (p + 1) → T) :
        ∃ b : (I.cocomplex.X r).obj.obj (op (S.W p t)),
          ((I.cocomplex.d r (r + 1)).hom.app (op (S.W p t))) b = c t := by
      have ht := hz t (r + 1) (by omega)
      rw [HomologicalComplex.exactAt_iff' _ r (r + 1) (r + 2) (by simp) (by simp),
        ShortComplex.ab_exact_iff] at ht
      exact ht (c t) (congrFun hc t)
    choose b hb using hlift
    exact ⟨b, funext hb⟩
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    rw [ShortComplex.quasiIso_iff_isIso_liftCycles _ (by simp) (by simp) (by simp)]
    let Q := (D.X p).sc' 0 0 1
    have hw : e.f 0 ≫ (D.X p).d 0 1 = 0 := by
      rw [e.comm]
      simp
    let k := Q.liftCycles (e.f 0) hw
    change IsIso k
    apply (ConcreteCategory.isIso_iff_bijective k).mpr
    constructor
    · intro x y hxy
      have h := congrArg (fun z ↦ Q.iCycles z) hxy
      change (k ≫ Q.iCycles) x = (k ≫ Q.iCycles) y at h
      rw [Q.liftCycles_i, he] at h
      funext t
      exact (AddCommGrpCat.mono_iff_injective ((F t).map (I.ι.f 0))).mp
        inferInstance (congrFun h t)
    · intro y
      let c := Q.iCycles y
      have hc : (D.X p).d 0 1 c = 0 := ConcreteCategory.congr_hom Q.iCycles_g y
      have hlift (t : Fin (p + 1) → T) : ∃ x : A.obj.obj (op (S.W p t)),
          ((I.ι.f 0).hom.app (op (S.W p t))) x = c t := by
        let z : (K t).cycles 0 :=
          ((K t).sc 0).abCyclesIso.inv ⟨c t, by
            change ((K t).sc 0).g (c t) = 0
            change (K t).d 0 ((ComplexShape.up ℕ).next 0) (c t) = 0
            rw [ComplexShape.next_eq' _ (by simp : (ComplexShape.up ℕ).Rel 0 1)]
            exact congrFun hc t⟩
        obtain ⟨x, hx⟩ :=
          (ConcreteCategory.bijective_of_isIso (I.toRightDerivedZero' (F t))).2 z
        refine ⟨x, ?_⟩
        have hh := congrArg (fun w ↦ (K t).iCycles 0 w) hx
        rw [← ConcreteCategory.comp_apply, I.toRightDerivedZero'_comp_iCycles] at hh
        exact hh.trans (((K t).sc 0).abCyclesIso_inv_apply_iCycles _)
      choose x hx using hlift
      refine ⟨x, ?_⟩
      apply (AddCommGrpCat.mono_iff_injective Q.iCycles).mp inferInstance
      change (k ≫ Q.iCycles) x = _
      rw [Q.liftCycles_i, he]
      exact funext hx

set_option backward.isDefEq.respectTransparency false in
private theorem site_beta_quasiIso
    {C : Type u} [SmallCategory C] {J : Precoverage C}
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (hA : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
      IsZero (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))).rightDerived r).obj A))
    (I : InjectiveResolution A) :
    QuasiIso (S.beta (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) I) := by
  let P := sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}
  let D := S.resolutionDoubleComplex P I
  let a : S.complex A.obj ⟶ D.flip.X 0 := (P ⋙ S.complexFunctor).map (I.ι.f 0)
  have ha : a ≫ D.flip.d 0 1 = 0 := by
    change (P ⋙ S.complexFunctor).map (I.ι.f 0) ≫
      (P ⋙ S.complexFunctor).map (I.cocomplex.d 0 1) = 0
    rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero]
  let b := S.beta P I ≫ (D.totalFlipIso (.up ℕ)).inv
  have hb : ∀ n : ℕ, b.f n = a.f n ≫ D.flip.ιTotal (.up ℕ) 0 n n (by simp) := by
    intro n
    dsimp [b, SiteCechComplex.beta]
    rw [Category.assoc, HomologicalComplex₂.ιTotal_totalFlipIso_f_inv]
    change _ ≫ ((-1 : ℤˣ) ^ (n * 0) • _) = _
    simp only [Nat.mul_zero, pow_zero, one_smul]
    rfl
  have hq : QuasiIso b := by
    apply HomologicalComplex₂.quasiIso_of_column_augmentation D.flip
      (S.complex A.obj) a ha b hb
    intro n
    exact site_beta_column_quasiIso S A hA I n _
      (CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _)
  have hcomp : b ≫ (D.totalFlipIso (.up ℕ)).hom = S.beta P I := by
    simp [b]
  rw [← hcomp]
  infer_instance

section AbelianEdgeProof

-- Use the augmentation interface without unfolding the sectionwise bicomplex.
attribute [local irreducible] SiteCechComplex.resolutionDoubleComplex
  SiteCechComplex.alpha SiteCechComplex.beta

/-- The canonical edge exists, is independent of resolutions, is natural for
additive sheaf maps, and is invertible on tuple-acyclic coefficients.
Source: Stacks 03AX, 03AZ, 03F7
(blueprint: lem-weil-pbc-acyclic-cech-edge-compatibility).

Proof: Construct the restriction augmentation alpha and the coefficient augmentation
beta componentwise in the total complex. Injective Cech acyclicity and the sheaf
condition in degree zero make alpha a quasi-isomorphism by first-quadrant
augmentation. Tuple acyclicity makes beta a quasi-isomorphism by the same criterion
on the transposed double complex; the symmetry sign is one on the augmentation
axis. Define the edge using a chosen injective resolution and the inverse of
H(alpha). A resolution lift induces a total map commuting with both augmentations.
The naturality formula for isoRightDerivedObj then transports the normalization
to every resolution and proves coefficient naturality. Normalization at the chosen
resolution determines the edge uniquely, so no separate total homotopy is needed.
-/
theorem exists_acyclicCechEdge
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type u} [Finite T] {U : C} (hU : IsTerminal U)
    (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom) :
    ∃! e : ∀ (A : Sheaf J.toGrothendieck AddCommGrpCat.{u})
      (_hA : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
        IsZero (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))).rightDerived r).obj A)) (q : ℕ),
      (S.cohomologyFunctor q).obj A.obj ⟶
        ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj A,
      (∀ A hA q, S.IsNormalizedEdge (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u})
        q (e A hA q) ∧ IsIso (e A hA q)) ∧
      (∀ (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}) hA
        (B : Sheaf J.toGrothendieck AddCommGrpCat.{u}) hB (g : A ⟶ B) (q : ℕ),
        (S.cohomologyFunctor q).map g.hom ≫ e B hB q =
          e A hA q ≫
            ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived
              q).map g) := by
  classical
  have _ := hU
  let P := sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}
  have hα (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (I : InjectiveResolution A) :
      QuasiIso (S.alpha P I) := site_alpha_quasiIso hcover S I
  let edge (A : Sheaf J.toGrothendieck AddCommGrpCat.{u})
      (_hA : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
        IsZero (((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj
          (op (S.W p t))).rightDerived r).obj A)) (q : ℕ) :=
    have := hα A (injectiveResolution A)
    S.edgeFromResolution P (injectiveResolution A) q
  have hnorm (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}) hA (q : ℕ) :
      S.IsNormalizedEdge P q (edge A hA q) := by
    intro L
    let I := injectiveResolution A
    have := hα A I
    have := hα A L
    refine ⟨S.augmentations P L, hα A L, ?_⟩
    have hn := S.resolutionEdge_naturality P (𝟙 A) q I L
      (S.augmentations P I) (S.augmentations P L)
      (InjectiveResolution.desc (𝟙 A) L I)
      (InjectiveResolution.desc_commutes_zero (𝟙 A) L I)
      (S.edgeFromResolution P I q) (S.edgeFromResolution P L q) (hα A L)
      (S.edgeFromResolution_spec P I q) (S.edgeFromResolution_spec P L q)
    have heq : edge A hA q = S.edgeFromResolution P L q := by
      simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using hn.symm
    rw [heq]
    exact S.edgeFromResolution_spec P L q
  refine ⟨edge, ⟨?_, ?_⟩, ?_⟩
  · intro A hA q
    refine ⟨hnorm A hA q, ?_⟩
    have := hα A (injectiveResolution A)
    have := site_beta_quasiIso S A hA (injectiveResolution A)
    change IsIso (S.edgeFromResolution P (injectiveResolution A) q)
    unfold SiteCechComplex.edgeFromResolution
    infer_instance
  · intro A hA B hB g q
    exact S.normalizedEdge_naturality P g q _ _ (hnorm A hA q) (hnorm B hB q)
  · intro e he
    funext A hA q
    exact S.normalizedEdge_unique P q _ _ (he.1 A hA q).1 (hnorm A hA q)

end AbelianEdgeProof

namespace SiteCechComplex

section SiteChange

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (u : C ⥤ D) {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
  (S : SiteCechComplex f hom)
  (S' : SiteCechComplex (fun t ↦ u.obj (f t)) (fun t ↦ u.map (hom t)))
  (c : ∀ (p : ℕ) (t : Fin (p + 1) → T), u.obj (S.W p t) ≅ S'.W p t)
  (hcpr : ∀ (p : ℕ) (t : Fin (p + 1) → T) (k : Fin (p + 1)),
    (c p t).hom ≫ S'.pr p t k = u.map (S.pr p t k))

include hcpr in
private theorem siteChange_indexMap {p q : ℕ} (t : Fin (p + 1) → T)
    (a : Fin (q + 1) → Fin (p + 1)) :
    S'.indexMap t a ≫ (c q (t ∘ a)).inv =
      (c p t).inv ≫ u.map (S.indexMap t a) := by
  apply (cancel_mono (c q (t ∘ a)).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have huni := S'.universal q (t ∘ a) (S'.W p t)
    (fun k ↦ S'.indexMap t a ≫ S'.pr q (t ∘ a) k)
    (fun k ↦ by rw [Category.assoc, Category.assoc, S'.comm])
  obtain ⟨b, _, hb⟩ := huni
  apply (hb _ (fun _ ↦ rfl)).trans
  apply Eq.symm
  apply hb
  intro k
  rw [Category.assoc, hcpr, Category.assoc, ← Functor.map_comp, S.indexMap_pr]
  rw [S'.indexMap_pr, ← hcpr p t (a k), Iso.inv_hom_id_assoc]

private def siteChangeCochains
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{u}} {G : Dᵒᵖ ⥤ AddCommGrpCat.{u}}
    (h : F ⟶ u.op ⋙ G) (n : ℕ) : S.cochains F n ⟶ S'.cochains G n :=
  AddCommGrpCat.ofHom
    { toFun := fun s t ↦ G.map (c n t).inv.op (h.app (op (S.W n t)) (s t))
      map_zero' := by funext t; simp
      map_add' := by intros; funext t; simp }

include hcpr in
private theorem siteChangeCochains_comm
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{u}} {G : Dᵒᵖ ⥤ AddCommGrpCat.{u}}
    (h : F ⟶ u.op ⋙ G) (n : ℕ) :
    S.siteChangeCochains u S' c h n ≫ (S'.complex G).d n (n + 1) =
      (S.complex F).d n (n + 1) ≫ S.siteChangeCochains u S' c h (n + 1) := by
  simp only [complex, CochainComplex.of_d]
  apply AddCommGrpCat.ext
  intro s
  funext t
  change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    G.map (S'.indexMap t j.succAbove).op
      (G.map (c n (t ∘ j.succAbove)).inv.op
        (h.app _ (s (t ∘ j.succAbove))))) =
    G.map (c (n + 1) t).inv.op
      (h.app _ (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        F.map (S.indexMap t j.succAbove).op (s (t ∘ j.succAbove))))
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [← ConcreteCategory.comp_apply, ← G.map_comp, ← op_comp,
    S.siteChange_indexMap u S' c hcpr, op_comp, G.map_comp]
  have hh := ConcreteCategory.congr_hom (h.naturality (S.indexMap t j.succAbove).op)
    (s (t ∘ j.succAbove))
  exact congrArg (G.map (c (n + 1) t).inv.op) hh.symm

private noncomputable def siteChangeComplexMap
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{u}} {G : Dᵒᵖ ⥤ AddCommGrpCat.{u}}
    (h : F ⟶ u.op ⋙ G) : S.complex F ⟶ S'.complex G :=
  CochainComplex.ofHom (S.siteChangeCochains u S' c h)
    (S.siteChangeCochains_comm u S' c hcpr h)

private theorem siteChangeCochains_naturality
    {F F' : Cᵒᵖ ⥤ AddCommGrpCat.{u}} {G G' : Dᵒᵖ ⥤ AddCommGrpCat.{u}}
    (h : F ⟶ u.op ⋙ G) (h' : F' ⟶ u.op ⋙ G') (a : F ⟶ F') (b : G ⟶ G')
    (hh : a ≫ h' = h ≫ Functor.whiskerLeft u.op b) (n : ℕ) :
    S.cochainsMap a n ≫ S.siteChangeCochains u S' c h' n =
      S.siteChangeCochains u S' c h n ≫ S'.cochainsMap b n := by
  apply AddCommGrpCat.ext
  intro s
  funext t
  have hw := congrArg (fun k ↦ k.app (op (S.W n t))) hh
  have hw' := ConcreteCategory.congr_hom hw (s t)
  change G'.map (c n t).inv.op (h'.app _ (a.app _ (s t))) =
    b.app _ (G.map (c n t).inv.op (h.app _ (s t)))
  change h'.app _ (a.app _ (s t)) = b.app _ (h.app _ (s t)) at hw'
  rw [hw']
  exact ConcreteCategory.congr_hom (b.naturality (c n t).inv.op).symm _

end SiteChange

section SiteChangeResolutions

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K]
  {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
  (S : SiteCechComplex f hom)
  (S' : SiteCechComplex (fun t ↦ u.obj (f t)) (fun t ↦ u.map (hom t)))
  (c : ∀ (p : ℕ) (t : Fin (p + 1) → T), u.obj (S.W p t) ≅ S'.W p t)
  (hcpr : ∀ (p : ℕ) (t : Fin (p + 1) → T) (k : Fin (p + 1)),
    (c p t).hom ≫ S'.pr p t k = u.map (S.pr p t k))
  {A : Sheaf J AddCommGrpCat.{u}} {B : Sheaf K AddCommGrpCat.{u}}
  (I : InjectiveResolution A) (L : InjectiveResolution B)
  (v : I.cocomplex ⟶
    ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).mapHomologicalComplex
      (.up ℕ)).obj L.cocomplex)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def siteChangeBicomplexMap :
    S.resolutionDoubleComplex (sheafToPresheaf J AddCommGrpCat.{u}) I ⟶
      S'.resolutionDoubleComplex (sheafToPresheaf K AddCommGrpCat.{u}) L where
  f p :=
    { f := fun r ↦ S.siteChangeCochains u S' c (v.f r).hom p
      comm' := by
        intro r s _
        have hv := congrArg (fun k ↦ k.hom) (v.comm r s)
        exact (S.siteChangeCochains_naturality u S' c (v.f r).hom (v.f s).hom
          (I.cocomplex.d r s).hom (L.cocomplex.d r s).hom hv.symm p).symm }
  comm' p q hpq := by
    have hq : p + 1 = q := hpq
    subst q
    apply HomologicalComplex.hom_ext
    intro r
    exact S.siteChangeCochains_comm u S' c hcpr (v.f r).hom p

private noncomputable def siteChangeTotalMap :
    (S.resolutionDoubleComplex (sheafToPresheaf J AddCommGrpCat.{u}) I).total (.up ℕ) ⟶
      (S'.resolutionDoubleComplex (sheafToPresheaf K AddCommGrpCat.{u}) L).total (.up ℕ) :=
  HomologicalComplex₂.total.map (S.siteChangeBicomplexMap J K u S' c hcpr I L v) (.up ℕ)

private def siteChangeSectionsMap :
    ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
        (.up ℕ)).obj I.cocomplex ⟶
      ((sheafToPresheaf K AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj U))).mapHomologicalComplex
          (.up ℕ)).obj L.cocomplex where
  f r := (v.f r).hom.app (op U)
  comm' r s _ := congrArg (fun k ↦ k.hom.app (op U)) (v.comm r s)

include hcpr in
set_option backward.isDefEq.respectTransparency false in
private theorem siteChange_alpha
    (d : S.Augmentations (sheafToPresheaf J AddCommGrpCat.{u}) I)
    (d' : S'.Augmentations (sheafToPresheaf K AddCommGrpCat.{u}) L) :
    d.alpha ≫ S.siteChangeTotalMap J K u S' c hcpr I L v =
      siteChangeSectionsMap J K u I L v ≫ d'.alpha := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, d.alpha_f, d'.alpha_f, Category.assoc,
    siteChangeTotalMap, HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply AddCommGrpCat.ext
  intro x
  funext t
  change (L.cocomplex.X n).obj.map (c 0 t).inv.op
    (((v.f n).hom.app (op (S.W 0 t)))
      ((I.cocomplex.X n).obj.map (S.pr 0 t 0 ≫ hom (t 0)).op x)) =
    (L.cocomplex.X n).obj.map (S'.pr 0 t 0 ≫ u.map (hom (t 0))).op
      (((v.f n).hom.app (op U)) x)
  have hn := ConcreteCategory.congr_hom
    ((v.f n).hom.naturality (S.pr 0 t 0 ≫ hom (t 0)).op) x
  change ((v.f n).hom.app (op (S.W 0 t)))
      ((I.cocomplex.X n).obj.map (S.pr 0 t 0 ≫ hom (t 0)).op x) =
    (L.cocomplex.X n).obj.map (u.map (S.pr 0 t 0 ≫ hom (t 0))).op
      (((v.f n).hom.app (op U)) x) at hn
  rw [hn, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  have hr : (c 0 t).inv ≫ u.map (S.pr 0 t 0 ≫ hom (t 0)) =
      S'.pr 0 t 0 ≫ u.map (hom (t 0)) := by
    rw [Functor.map_comp, ← hcpr 0 t 0, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hr]

include hcpr in
set_option backward.isDefEq.respectTransparency false in
private theorem siteChange_beta
    (h : A ⟶ (u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj B)
    (hv : I.ι.f 0 ≫ v.f 0 = h ≫
      (u.sheafPushforwardContinuous AddCommGrpCat.{u} J K).map (L.ι.f 0))
    (d : S.Augmentations (sheafToPresheaf J AddCommGrpCat.{u}) I)
    (d' : S'.Augmentations (sheafToPresheaf K AddCommGrpCat.{u}) L) :
    S.siteChangeComplexMap u S' c hcpr h.hom ≫ d'.beta =
      d.beta ≫ S.siteChangeTotalMap J K u S' c hcpr I L v := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, d.beta_f, d'.beta_f, Category.assoc,
    siteChangeTotalMap, HomologicalComplex₂.ιTotal_map]
  have hh := S.siteChangeCochains_naturality u S' c h.hom (v.f 0).hom
    (I.ι.f 0).hom (L.ι.f 0).hom (congrArg (fun k ↦ k.hom) hv) n
  have hh' := congrArg (fun k ↦ k ≫
    (S'.resolutionDoubleComplex (sheafToPresheaf K AddCommGrpCat.{u}) L).ιTotal
      (.up ℕ) n 0 n (by simp)) hh.symm
  simp only [Category.assoc] at hh'
  exact hh' 

end SiteChangeResolutions

end SiteCechComplex

set_option backward.isDefEq.respectTransparency false in
private theorem siteChange_resolution_lift
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : C ⥤ D)
    (hc : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map u ∈ K (u.obj X))
    (hp : ∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), R a → PreservesLimit (cospan a b) u)
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    {A : Sheaf J.toGrothendieck AddCommGrpCat.{u}}
    {B : Sheaf K.toGrothendieck AddCommGrpCat.{u}}
    (h : A ⟶ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
      J.toGrothendieck K.toGrothendieck).obj B)
    (I : InjectiveResolution A) (L : InjectiveResolution B) :
    ∃ v : I.cocomplex ⟶ ((u.sheafPushforwardContinuous AddCommGrpCat.{u}
      J.toGrothendieck K.toGrothendieck).mapHomologicalComplex (.up ℕ)).obj L.cocomplex,
      I.ι.f 0 ≫ v.f 0 = h ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).map (L.ι.f 0) := by
  let F := sheafPullback u AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck
  let G := u.sheafPushforwardContinuous AddCommGrpCat.{u}
    J.toGrothendieck K.toGrothendieck
  obtain ⟨hadd, hlim, hcolim, _, _⟩ := sitePullback_abelian_exact J K u hc hp
  let : F.Additive := hadd
  let : PreservesFiniteLimits F := hlim
  let : PreservesFiniteColimits F := hcolim
  let : G.Additive := ⟨by intro X Y a b; ext V; rfl⟩
  exact adjunction_resolution_lift F G
    (sheafAdjunctionContinuous u AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck) I L h

section SiteChangeEdgeProof

-- Use the augmentation interface without unfolding the sectionwise bicomplex.
attribute [local irreducible] SiteCechComplex.resolutionDoubleComplex
  SiteCechComplex.alpha SiteCechComplex.beta

-- Preserve the original names of universally quantified proof binders.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency true in
/-- Normalized edges commute with site change and an additive coefficient map.
Source: Stacks 03AX and 03F7
(blueprint: lem-weil-pbc-acyclic-cech-edge-compatibility).

Proof: Exact inverse image sends the source injective resolution to a resolution.
Lift the adjoint of h from this resolution to the target injective resolution,
then apply the adjunction unit to obtain v with its strict augmentation equation.
For any such v, its section maps define w and the tuple comparison isomorphisms
define the Cech map hC. The product universal properties show that the tuple
isomorphisms commute with faces. Restriction naturality and the augmentation
equation give the two literal comparison squares between total complexes.
Apply homology to the squares, substitute both edge normalizations, and cancel
the target alpha and resolution isomorphism.
-/
theorem acyclicCechEdge_siteChange
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : C ⥤ D)
    (hc : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map u ∈ K (u.obj X))
    (hp : ∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), R a → PreservesLimit (cospan a b) u)
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    {T : Type u} [Finite T] {U : C} (hU : IsTerminal U) (huU : IsTerminal (u.obj U))
    (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (S' : SiteCechComplex (fun t ↦ u.obj (f t)) (fun t ↦ u.map (hom t)))
    (c : ∀ (p : ℕ) (t : Fin (p + 1) → T), u.obj (S.W p t) ≅ S'.W p t)
    (hcpr : ∀ (p : ℕ) (t : Fin (p + 1) → T) (k : Fin (p + 1)),
      (c p t).hom ≫ S'.pr p t k = u.map (S.pr p t k))
    (A : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (B : Sheaf K.toGrothendieck AddCommGrpCat.{u})
    (h : A ⟶ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
      J.toGrothendieck K.toGrothendieck).obj B)
    (hA : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
      IsZero (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))).rightDerived r).obj A))
    (hB : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
      IsZero (((sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (S'.W p t))).rightDerived r).obj B))
    (q : ℕ)
    (eA : (S.cohomologyFunctor q).obj A.obj ⟶
      ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj A)
    (eB : (S'.cohomologyFunctor q).obj B.obj ⟶
      ((sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj U))).rightDerived q).obj B)
    (heA : S.IsNormalizedEdge (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) q eA)
    (heB : S'.IsNormalizedEdge (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u}) q eB)
    (I : InjectiveResolution A) (L : InjectiveResolution B) :
    (∃ v : I.cocomplex ⟶
      ((u.sheafPushforwardContinuous AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj L.cocomplex,
      I.ι.f 0 ≫ v.f 0 = h ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).map (L.ι.f 0)) ∧
    ∀ (v : I.cocomplex ⟶
      ((u.sheafPushforwardContinuous AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj L.cocomplex)
      (hv : I.ι.f 0 ≫ v.f 0 = h ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).map (L.ι.f 0)),
      ∃ (w : ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex ⟶
        ((sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj U))).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj L.cocomplex)
        (hC : S.complex A.obj ⟶ S'.complex B.obj),
        (∀ n : ℕ, w.f n = (v.f n).hom.app (op U)) ∧
        (∀ (n : ℕ) (s : S.cochains A.obj n) (t : Fin (n + 1) → T),
          (hC.f n s) t = B.obj.map (c n t).inv.op ((h.hom.app (op (S.W n t))) (s t))) ∧
        eA ≫ (I.isoRightDerivedObj (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom ≫
            HomologicalComplex.homologyMap w q ≫
              (L.isoRightDerivedObj (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
                (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj U))) q).inv =
          HomologicalComplex.homologyMap hC q ≫ eB := by
  have _ := hU
  have _ := huU
  have _ := hcover
  have _ := hA
  have _ := hB
  refine ⟨siteChange_resolution_lift J K u hc hp h I L, ?_⟩
  intro v hv
  let w := SiteCechComplex.siteChangeSectionsMap (U := U)
    J.toGrothendieck K.toGrothendieck u I L v
  let hC := S.siteChangeComplexMap u S' c hcpr h.hom
  refine ⟨w, hC, fun _ ↦ rfl, fun _ _ _ ↦ rfl, ?_⟩
  obtain ⟨d, _, heA⟩ := heA I
  obtain ⟨d', hd', heB⟩ := heB L
  have hα'iso : IsIso (HomologicalComplex.homologyMap d'.alpha q) :=
    (quasiIsoAt_iff_isIso_homologyMap d'.alpha q).mp
      (hd'.quasiIsoAt q)
  let F := sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let G := sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
    (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj U))
  have hα := congrArg (fun k ↦ HomologicalComplex.homologyMap k q)
    (S.siteChange_alpha J.toGrothendieck K.toGrothendieck u S' c hcpr I L v d d')
  have hβ := congrArg (fun k ↦ HomologicalComplex.homologyMap k q)
    (S.siteChange_beta J.toGrothendieck K.toGrothendieck u S' c hcpr I L v h hv d d')
  simp only [HomologicalComplex.homologyMap_comp] at hα hβ
  exact edge_comparison_square (I.isoRightDerivedObj F q) (L.isoRightDerivedObj G q)
    (hα'iso := hα'iso) hα hβ heA heB

end SiteChangeEdgeProof

section ForgetModules

variable {C : Type u} [SmallCategory C] (J : Precoverage C)
  [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
  (R : Sheaf J.toGrothendieck RingCat.{u})
  {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
  (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)

include hcover in
set_option backward.isDefEq.respectTransparency false in
private theorem module_alpha_quasiIso {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) :
    QuasiIso (S.alpha (SheafOfModules.toSheaf R ⋙
      sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) I) := by
  let P := SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}
  apply HomologicalComplex₂.quasiIso_of_column_augmentation
    (S.resolutionDoubleComplex P I) _ (S.restrictionToZero P I)
    (S.restrictionToZero_d P I) (S.alpha P I) (fun _ ↦ rfl)
  intro n
  apply site_row_augmentation_quasiIso hcover S
    ((SheafOfModules.toSheaf R).obj (I.cocomplex.X n))
  · exact fun r hr ↦ injective_module_cech_cohomology_isZero J R
      (I.cocomplex.X n) f hom hcover S r hr
  · exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end ForgetModules

section ForgetComparison

variable {C : Type u} [SmallCategory C] (J : Precoverage C)
  {E : Type*} [Category* E] [Abelian E]
  (Q : E ⥤ Sheaf J.toGrothendieck AddCommGrpCat.{u}) [Q.Additive]
  {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
  (S : SiteCechComplex f hom)

variable {M : E} (I : InjectiveResolution M)
  (L : InjectiveResolution (Q.obj M))
  (k : (Q.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
    L.cocomplex)

private noncomputable def forgetTotalMap :
    (S.resolutionDoubleComplex (Q ⋙
      sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) I).total (.up ℕ) ⟶
    (S.resolutionDoubleComplex (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) L).total
      (.up ℕ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ _ _).map
      (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        S.complexFunctor).mapHomologicalComplex (.up ℕ)).map k)) (.up ℕ)

set_option backward.isDefEq.respectTransparency false in
private theorem forget_alpha
    (d : S.Augmentations (Q ⋙
      sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) I)
    (d' : S.Augmentations (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) L) :
    d.alpha ≫ forgetTotalMap J Q S I L k =
      ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex (.up ℕ)).map k ≫
          d'.alpha := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, d.alpha_f, d'.alpha_f, Category.assoc,
    forgetTotalMap, HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply AddCommGrpCat.ext
  intro s
  funext t
  exact ConcreteCategory.congr_hom
    ((k.f n).hom.naturality (S.pr 0 t 0 ≫ hom (t 0)).op) s

set_option backward.isDefEq.respectTransparency false in
private theorem forget_beta
    (hk : Q.map (I.ι.f 0) ≫ k.f 0 = L.ι.f 0)
    (d : S.Augmentations (Q ⋙
      sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) I)
    (d' : S.Augmentations (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) L) :
    d.beta ≫ forgetTotalMap J Q S I L k = d'.beta := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, d.beta_f, d'.beta_f, Category.assoc,
    forgetTotalMap, HomologicalComplex₂.ιTotal_map]
  have hh := congrArg (fun a ↦ ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
    S.complexFunctor).map a).f n) hk
  have hh' := congrArg (fun a ↦ a ≫
    (S.resolutionDoubleComplex (sheafToPresheaf J.toGrothendieck
      AddCommGrpCat.{u}) L).ιTotal (.up ℕ) n 0 n (by simp)) hh
  simp only [Functor.map_comp, HomologicalComplex.comp_f, Category.assoc] at hh'
  exact hh'

variable [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]

set_option backward.isDefEq.respectTransparency false in
private theorem forget_resolution_lift :
    ∃ k : (Q.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      L.cocomplex, Q.map (I.ι.f 0) ≫ k.f 0 = L.ι.f 0 := by
  obtain ⟨k, hk⟩ := exact_resolution_lift Q I L (𝟙 (Q.obj M))
  exact ⟨k, by simpa only [Category.id_comp] using hk⟩

variable [EnoughInjectives E]

attribute [local irreducible] SiteCechComplex.resolutionDoubleComplex
  SiteCechComplex.alpha SiteCechComplex.beta

set_option backward.isDefEq.respectTransparency true in
private theorem forget_normalization
    (q : ℕ)
    (c : (((Q ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj M) ≅
      (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj (Q.obj M)))
    (hc : ∀ (I : InjectiveResolution M) (L : InjectiveResolution (Q.obj M))
      (k : (Q.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ L.cocomplex)
      (_hk : Q.map (I.ι.f 0) ≫ k.f 0 = L.ι.f 0),
      c.hom ≫ (L.isoRightDerivedObj (sheafToPresheaf J.toGrothendieck
        AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom =
      (I.isoRightDerivedObj (Q ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom ≫
      HomologicalComplex.homologyMap
        (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
            (.up ℕ)).map k) q)
    (hrow : ∀ I : InjectiveResolution M,
      QuasiIso (S.alpha (Q ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) I))
    (eA : (S.cohomologyFunctor q).obj (Q.obj M).obj ⟶
      ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj (Q.obj M))
    (heA : S.IsNormalizedEdge (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u})
      q eA) : S.IsNormalizedEdge
        (Q ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) q (eA ≫ c.inv) := by
  let F := sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)
  intro I
  let L := injectiveResolution (Q.obj M)
  obtain ⟨k, hk⟩ := forget_resolution_lift J Q I L
  obtain ⟨d', hd', he⟩ := heA L
  have hα'iso : IsIso (HomologicalComplex.homologyMap d'.alpha q) :=
    (quasiIsoAt_iff_isIso_homologyMap d'.alpha q).mp
      (hd'.quasiIsoAt q)
  let P := Q ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}
  let d := S.augmentations P I
  have hd : QuasiIso d.alpha := hrow I
  have hαiso : IsIso (HomologicalComplex.homologyMap d.alpha q) :=
    (quasiIsoAt_iff_isIso_homologyMap d.alpha q).mp
      (hd.quasiIsoAt q)
  let V := forgetTotalMap J Q S I L k
  let w := (F.mapHomologicalComplex (.up ℕ)).map k
  have hαraw := congrArg (fun a ↦ HomologicalComplex.homologyMap a q)
    (forget_alpha J Q S I L k d d')
  have hβraw := congrArg (fun a ↦ HomologicalComplex.homologyMap a q)
    (forget_beta J Q S I L k hk d d')
  have hα := ((HomologicalComplex.homologyMap_comp d.alpha V q).symm.trans
    hαraw).trans (HomologicalComplex.homologyMap_comp w d'.alpha q)
  have hβ := (HomologicalComplex.homologyMap_comp d.beta V q).symm.trans hβraw
  refine ⟨d, hd, ?_⟩
  exact transport_edge_normalization c
    (I.isoRightDerivedObj (Q ⋙ F) q)
    (L.isoRightDerivedObj F q) (hαiso := hαiso) (hα'iso := hα'iso)
    hα hβ (hc I L k hk) he

end ForgetComparison

section ModuleEdgeProof

-- Use the augmentation interface without unfolding the sectionwise bicomplex.
attribute [local irreducible] SiteCechComplex.resolutionDoubleComplex
  SiteCechComplex.alpha SiteCechComplex.beta

set_option backward.isDefEq.respectTransparency true in
private theorem normalized_site_edge_isIso
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type u} [Finite T] {U : C} (hU : IsTerminal U)
    {f : T → C} {hom : ∀ t, f t ⟶ U}
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (A : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (hA : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
      IsZero (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))).rightDerived r).obj A))
    (q : ℕ)
    (eA : (S.cohomologyFunctor q).obj A.obj ⟶
      ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj A)
    (heA : S.IsNormalizedEdge (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u})
      q eA) : IsIso eA := by
  obtain ⟨e, he, _⟩ := exists_acyclicCechEdge J hU f hom hcover S
  have heq := S.normalizedEdge_unique
    (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) q eA (e A hA q) heA
    (he.1 _ hA q).1
  rw [heq]
  exact (he.1 _ hA q).2

-- Preserve the original names of universally quantified proof binders.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 800000 in
-- Comparing two derived section functors requires repeated resolution elaboration.
/-- Forgetting scalar multiplication preserves the canonical normalized edge.
The comparison c is specified both by all resolution lifts and by the unique
morphism of universal delta-functors inducing the identity on sections.
Source: Stacks 03FC, 03FD and 03AX
(blueprint: lem-weil-pbc-acyclic-cech-edge-compatibility).

Proof: Use module_abelian_evaluation_comparison for the natural isomorphism c,
its degree-zero normalization, and its formula for every resolution lift.
Represent the universal delta-functor of module evaluation in the two families
of functors through c; universality makes its identity morphism the unique
morphism with the prescribed degree-zero component. The resolution formula
follows by cancelling the target resolution isomorphism.
For an edge eA, put eM = eA followed by c inverse. Forgetting is exact, so the
forgotten module resolution admits an augmentation-preserving map k to an
abelian injective resolution. Injective-module Cech acyclicity and the sheaf
condition make the module restriction augmentation alpha a quasi-isomorphism.
Apply Cech to k to obtain a total map V commuting with both augmentations.
The formula for c makes H(sections(k)) invertible; the alpha square then makes
H(V) invertible. Cancel H(V) and use the beta square and normalization of eA
to prove normalization of eM. The abelian edge theorem makes eA invertible,
hence eM is invertible. Normalization at one resolution proves uniqueness.
-/
theorem acyclicCechEdge_forgetModules
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{u})
    {T : Type u} [Finite T] {U : C} (hU : IsTerminal U)
    (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom) :
    ∃ c : ∀ q : ℕ,
      (SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q ≅
      SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q,
      (∀ M : SheafOfModules.{u} R,
        (SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).toRightDerivedZero.app M ≫
            (c 0).hom.app M =
          (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).toRightDerivedZero.app
              ((SheafOfModules.toSheaf R).obj M)) ∧
      (∃ (G H : CohomologicalDeltaFunctor (SheafOfModules.{u} R) AddCommGrpCat.{u})
        (g : ∀ q : ℕ, G.F q ≅
          (SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q)
        (h : ∀ q : ℕ, H.F q ≅ SheafOfModules.toSheaf R ⋙
          (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q),
        G.IsUniversal ∧ H.IsUniversal ∧
          ∃ t : CohomologicalDeltaFunctor.Hom G H,
            (∀ q : ℕ, (g q).inv ≫ t.app q ≫ (h q).hom = (c q).hom) ∧
            ∀ t' : CohomologicalDeltaFunctor.Hom G H,
              (g 0).inv ≫ t'.app 0 ≫ (h 0).hom = (c 0).hom → t' = t) ∧
      (∀ (M : SheafOfModules.{u} R) (P : InjectiveResolution M)
        (L : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
        (k : ((SheafOfModules.toSheaf R).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj P.cocomplex ⟶ L.cocomplex)
        (hk : (SheafOfModules.toSheaf R).map (P.ι.f 0) ≫ k.f 0 = L.ι.f 0)
        (q : ℕ),
        (c q).hom.app M =
          (P.isoRightDerivedObj (SheafOfModules.toSheaf R ⋙
            sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
              (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).hom ≫
          HomologicalComplex.homologyMap
            (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
              (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
                (ComplexShape.up ℕ)).map k) q ≫
          (L.isoRightDerivedObj (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) q).inv) ∧
      (∀ (M : SheafOfModules.{u} R)
        (hM : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
          IsZero (((SheafOfModules.toSheaf R ⋙
            sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
              (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))).rightDerived r).obj M))
        (hA : ∀ (p : ℕ) (t : Fin (p + 1) → T) (r : ℕ), 0 < r →
          IsZero (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op (S.W p t))).rightDerived r).obj
              ((SheafOfModules.toSheaf R).obj M)))
        (q : ℕ)
        (eA : (S.cohomologyFunctor q).obj ((SheafOfModules.toSheaf R).obj M).obj ⟶
          ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj
              ((SheafOfModules.toSheaf R).obj M))
        (heA : S.IsNormalizedEdge
          (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u})
            (A := (SheafOfModules.toSheaf R).obj M) q eA),
        ∃! eM : (S.cohomologyFunctor q).obj ((SheafOfModules.toSheaf R).obj M).obj ⟶
          ((SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj M,
          S.IsNormalizedEdge
            (SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u})
              (A := M) q eM ∧ IsIso eM ∧ eM ≫ (c q).hom.app M = eA) := by
  classical
  let F := sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let P := SheafOfModules.toSheaf R ⋙ F
  have : PreservesFiniteColimits (SheafOfModules.toSheaf R) :=
    (moduleSheaves_colimits_forgetful R).2.2.1
  obtain ⟨c, hc0, hc⟩ := module_abelian_evaluation_comparison J R U
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro M
    exact NatTrans.congr_app hc0 M
  · exact universal_derived_comparison P
      (fun q ↦ SheafOfModules.toSheaf R ⋙ F.rightDerived q) c
  · intro M I L k hk q
    exact resolution_formula_from_square (L.isoRightDerivedObj F q) (hc M I L k hk q)
  · intro M hM hA q eA heA
    have _ := hM
    have heIso : IsIso eA := normalized_site_edge_isIso J hU hcover S
      ((SheafOfModules.toSheaf R).obj M) hA q eA heA
    let eM := eA ≫ (c q).inv.app M
    have hn : S.IsNormalizedEdge (SheafOfModules.toSheaf R ⋙
        sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) q eM :=
      forget_normalization J (SheafOfModules.toSheaf R) S q ((c q).app M)
        (fun I L k hk ↦ hc M I L k hk q)
        (fun I ↦ module_alpha_quasiIso J R hcover S I) eA heA
    have hMiso : IsIso eM := IsIso.comp_isIso' heIso inferInstance
    refine ⟨eM, ⟨hn, hMiso, ?_⟩, ?_⟩
    · simp [eM]
    · intro e' he'
      exact S.normalizedEdge_unique (SheafOfModules.toSheaf R ⋙
        sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) q e' eM he'.1 hn

end ModuleEdgeProof

end CategoryTheory
