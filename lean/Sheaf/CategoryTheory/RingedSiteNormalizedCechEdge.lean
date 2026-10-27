/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCechEdgeNormalization
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Normalized Čech edges for arbitrary module coefficients

Source: Stacks 01FD, 03AX, 03FC and 08J6.
(blueprint: lem-weil-pbc-ringed-site-normalized-cech-edge)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

attribute [local instance] Functor.additive_of_preserves_binary_products

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

end Comparison

end SiteCechComplex

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

/-- Every coefficient module has one normalized Čech edge, without an acyclicity
assumption on the coefficient.

Source: Stacks 03AX and 03FC
(blueprint: lem-weil-pbc-ringed-site-normalized-cech-edge).

Proof: For an injective resolution construct alpha by restriction of global sections
in Čech degree zero, and beta from the coefficient augmentation in resolution degree
zero. The sheaf equalizer identifies degree-zero row cohomology with global sections;
positive row cohomology vanishes for injective modules. First-quadrant augmentation
therefore makes alpha a quasi-isomorphism with Čech degree first. Define the edge
using beta followed by the inverse homology map of alpha and the inverse canonical
resolution comparison. A strict comparison between any two injective resolutions
commutes with both augmentations termwise. Its canonical global homology comparison
proves normalization for every resolution. Finally the displayed degreewise formulas
make any two alphas equal and any two betas equal. Cancellation at one resolution
proves uniqueness. The argument includes empty covers and degree zero.
-/
theorem ringedSite_normalized_cech_edge
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{u})
    [EnoughInjectives (ringedSiteModules.{u} R)]
    (M : ringedSiteModules.{u} R)
    {X : C} {I : Type u} [Finite I]
    (U : I → C) (v : ∀ i, U i ⟶ X)
    (hU : Presieve.ofArrows U v ∈ J X) (S : SiteCechComplex U v) (q : ℕ) :
    ∃! e : (S.cohomologyFunctor q).obj M.val.presheaf ⟶
      (((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).rightDerived q).obj M,
      S.IsNormalizedEdge (SheafOfModules.forget R ⋙
        PresheafOfModules.toPresheaf R.obj) q e := by
  classical
  let P := SheafOfModules.toSheaf R ⋙ sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}
  have hα (I : InjectiveResolution M) : QuasiIso (S.alpha P I) :=
    module_alpha_quasiIso J R hU S I
  let I₀ := injectiveResolution M
  have := hα I₀
  let e := S.edgeFromResolution P I₀ q
  have he : S.IsNormalizedEdge P q e := by
    intro I
    have := hα I
    refine ⟨S.augmentations P I, hα I, ?_⟩
    have hn := S.resolutionEdge_naturality P (𝟙 M) q I₀ I
      (S.augmentations P I₀) (S.augmentations P I)
      (InjectiveResolution.desc (𝟙 M) I I₀)
      (InjectiveResolution.desc_commutes_zero (𝟙 M) I I₀)
      e (S.edgeFromResolution P I q) (hα I)
      (S.edgeFromResolution_spec P I₀ q) (S.edgeFromResolution_spec P I q)
    have heq : e = S.edgeFromResolution P I q := by
      simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using hn.symm
    rw [heq]
    exact S.edgeFromResolution_spec P I q
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact S.normalizedEdge_unique P q e' e he' he

end CategoryTheory
