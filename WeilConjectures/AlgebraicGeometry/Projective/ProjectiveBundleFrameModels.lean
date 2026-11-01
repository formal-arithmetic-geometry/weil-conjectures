/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebra
import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.RelativeProjectiveSpace
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import WeilConjectures.AlgebraicGeometry.PicardUnitComposition
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSectionChart
public import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjFreeComparison
public import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjNormalizedDescent
public import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjOpenComparison

/-! # Projective bundles on frame charts

Source: Stacks Project, Tags 01OB, 01O3, 01OE.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundleTensorPullbackIso projectiveBundlePullbackId projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  projectiveBundlePullbackSection

/-- A symmetric-algebra projective bundle with its normalized quotient and charts for
all frames. Properness, invertibility, and base-change coherence are separate consequences.
Source: Stacks Project, Tags 01OB and 01OE
(blueprint: lem-pur-projective-bundle-frame-models). -/
structure ProjectiveBundleFrameModels (n : ℕ) where
  bundle : ∀ (B : Scheme.{u}) (F : B.Modules)
    (_hF : projectiveBundleRank B n F), ProjectiveBundleRealization B F
  frame : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F)
    (U : B.Opens) (e : B.ModuleFrame F U (n + 1)),
      ProjectiveBundleFrameChart (bundle B F hF) n U e

private theorem normalized_adjunction_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    projectiveBundlePullbackAdjunction g = Scheme.Modules.tensorPullbackSectionAdjunction g := by
  unfold projectiveBundlePullbackAdjunction
  exact (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction g).unique
    (fun M U m ↦ Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction g)
      M (op U) m)
    (Classical.choose_spec (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction g)).1

private theorem normalized_section_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {U : Y.Opens} (m : Γ(M, U)) :
    projectiveBundlePullbackSection g m = Scheme.Modules.tensorPullbackSection g M U m := by
  unfold projectiveBundlePullbackSection projectiveBundlePullbackAdjunction
  exact Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction g) M (op U) m

private theorem symmetricDegree_eq (R M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] (d : ℕ) :
    Scheme.symmetricDegree R M d = (SymmetricAlgebra.ι R M).range ^ d := by
  have h := SymmetricAlgebra.graded_span_pure_tensors R M d
  simp only [Submodule.map_pow, ← LinearMap.range_comp] at h
  change (SymmetricAlgebra.ι R M).range ^ d = _ at h
  simpa only [Scheme.symmetricDegree, List.prod_ofFn] using h.symm

private noncomputable def symmetricData {B : Scheme.{u}} (F : B.Modules)
    [F.IsQuasicoherent] : B.SymmetricGradedAlgebraData F where
  data := SymmetricAlgebraSheaf.gradedAlgebraData F
  sectionEquiv _ := AlgEquiv.refl
  sectionEquiv_grade U d x := by
    change x ∈ Scheme.symmetricDegree _ _ d ↔ x ∈ (SymmetricAlgebra.ι _ _).range ^ d
    rw [symmetricDegree_eq]
  sectionEquiv_restriction _ _ := rfl

private theorem comp_comparison_mate {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv
      ((projectiveBundlePullbackAdjunction g).comp (projectiveBundlePullbackAdjunction f))
      (projectiveBundlePullbackAdjunction (f ≫ g))
      (projectiveBundlePullbackComp f g).inv = (Scheme.Modules.pushforwardComp f g).hom := by
  let tf := projectiveBundlePullbackAdjunction f
  let tg := projectiveBundlePullbackAdjunction g
  let tfg := projectiveBundlePullbackAdjunction (f ≫ g)
  let pf := Scheme.Modules.pullbackPushforwardAdjunction f
  let pg := Scheme.Modules.pullbackPushforwardAdjunction g
  let pfg := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  unfold projectiveBundlePullbackComp
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc]
  change conjugateEquiv (tg.comp tf) tfg
    ((projectiveBundleTensorPullbackIso (f ≫ g)).hom ≫
      (Scheme.Modules.pullbackComp f g).inv ≫
      Functor.whiskerLeft (Scheme.Modules.pullback g) (projectiveBundleTensorPullbackIso f).inv ≫
      Functor.whiskerRight (projectiveBundleTensorPullbackIso g).inv
        (Scheme.Modules.tensorPullback f)) = _
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp (tg.comp tf) (pg.comp tf) tfg]
  rw [← conjugateEquiv_comp (pg.comp tf) (pg.comp pf) tfg]
  rw [← conjugateEquiv_comp (pg.comp pf) pfg tfg]
  rw [conjugateEquiv_whiskerRight tg pg tf, conjugateEquiv_whiskerLeft tf pf pg]
  dsimp only [tf, tg, tfg, pf, pg, pfg]
  simp only [projectiveBundleTensorPullbackIso, projectiveBundlePullbackAdjunction,
    Adjunction.leftAdjointUniq, Iso.symm_inv, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_hom, conjugateIsoEquiv_symm_apply_inv,
    Equiv.apply_symm_apply, Iso.refl_hom, Iso.refl_inv,
    Category.comp_id, Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  cat_disch

private theorem leftAdjointUniq_changeRight
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    (a.leftAdjointUniq (b.ofNatIsoRight e)).symm =
      (conjugateIsoEquiv a b).symm e.symm := by
  apply Iso.ext
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv, conjugateEquiv,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit]

private theorem comp_comparison_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    projectiveBundlePullbackComp f g = (Scheme.Modules.tensorPullbackSectionComp f g).symm := by
  suffices (projectiveBundlePullbackComp f g).symm =
      Scheme.Modules.tensorPullbackSectionComp f g by
    exact congrArg Iso.symm this
  apply Iso.ext
  apply (conjugateEquiv
    ((projectiveBundlePullbackAdjunction g).comp (projectiveBundlePullbackAdjunction f))
    (projectiveBundlePullbackAdjunction (f ≫ g))).injective
  change conjugateEquiv _ _ (projectiveBundlePullbackComp f g).inv = _
  rw [comp_comparison_mate]
  rw [normalized_adjunction_eq, normalized_adjunction_eq, normalized_adjunction_eq]
  have h := congrArg Iso.inv (leftAdjointUniq_changeRight
    (Scheme.Modules.tensorPullbackSectionAdjunction (f ≫ g))
    ((Scheme.Modules.tensorPullbackSectionAdjunction g).comp
      (Scheme.Modules.tensorPullbackSectionAdjunction f)) (Scheme.Modules.pushforwardComp f g))
  change (Scheme.Modules.tensorPullbackSectionComp f g).hom =
    (conjugateEquiv
      ((Scheme.Modules.tensorPullbackSectionAdjunction g).comp
        (Scheme.Modules.tensorPullbackSectionAdjunction f))
      (Scheme.Modules.tensorPullbackSectionAdjunction (f ≫ g))).symm
      (Scheme.Modules.pushforwardComp f g).hom at h
  rw [h, Equiv.apply_symm_apply]

private theorem comp_eq_mate {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    projectiveBundlePullbackComp f g = Adjunction.leftAdjointCompIso
      (projectiveBundlePullbackAdjunction g) (projectiveBundlePullbackAdjunction f)
      (projectiveBundlePullbackAdjunction (f ≫ g)) (Scheme.Modules.pushforwardComp f g) := by
  apply Iso.ext_inv
  apply (conjugateEquiv
    ((projectiveBundlePullbackAdjunction g).comp (projectiveBundlePullbackAdjunction f))
    (projectiveBundlePullbackAdjunction (f ≫ g))).injective
  rw [comp_comparison_mate, Adjunction.conjugateEquiv_leftAdjointCompIso_inv]

private theorem mate_transport
    {C D E I : Type*} [Category C] [Category D] [Category E]
    (L : I → C ⥤ E) (R : I → E ⥤ C) (adj : ∀ i, L i ⊣ R i)
    {F : C ⥤ D} {G : D ⥤ E} {F' : D ⥤ C} {G' : E ⥤ D}
    (aF : F ⊣ F') (aG : G ⊣ G') {i i' : I} (e : i = i')
    (d : G' ⋙ F' ≅ R i) :
    Adjunction.leftAdjointCompIso aF aG (adj i')
        (d ≪≫ eqToIso (congrArg R e)) =
      Adjunction.leftAdjointCompIso aF aG (adj i) d ≪≫ eqToIso (congrArg L e) := by
  cases e
  simp

private theorem pushforward_assoc {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward f)
        (Scheme.Modules.pushforwardComp g h) ≪≫
        Scheme.Modules.pushforwardComp f (g ≫ h) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.pushforwardComp f g)
          (Scheme.Modules.pushforward h) ≪≫
        Scheme.Modules.pushforwardComp (f ≫ g) h ≪≫
        eqToIso (congrArg Scheme.Modules.pushforward (Category.assoc f g h)) := by
  apply Iso.ext
  ext M U x
  rfl

private theorem comp_assoc {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (Scheme.Modules.tensorPullback h)
        (projectiveBundlePullbackComp f g) ≪≫
        projectiveBundlePullbackComp (f ≫ g) h ≪≫
        projectiveBundlePullbackCongr (Category.assoc f g h) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (projectiveBundlePullbackComp g h)
          (Scheme.Modules.tensorPullback f) ≪≫ projectiveBundlePullbackComp f (g ≫ h) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (projectiveBundlePullbackAdjunction h) (projectiveBundlePullbackAdjunction g)
    (projectiveBundlePullbackAdjunction f) (projectiveBundlePullbackAdjunction (g ≫ h))
    (projectiveBundlePullbackAdjunction (f ≫ g))
    (projectiveBundlePullbackAdjunction (f ≫ g ≫ h))
    (Scheme.Modules.pushforwardComp g h) (Scheme.Modules.pushforwardComp f g)
    (Scheme.Modules.pushforwardComp (f ≫ g) h ≪≫
      eqToIso (congrArg Scheme.Modules.pushforward (Category.assoc f g h)))
    (Scheme.Modules.pushforwardComp f (g ≫ h)) (pushforward_assoc f g h)
  rw [mate_transport Scheme.Modules.tensorPullback Scheme.Modules.pushforward
    projectiveBundlePullbackAdjunction _ _ (Category.assoc f g h)] at hh
  simpa only [← comp_eq_mate, projectiveBundlePullbackCongr, Iso.trans_assoc] using hh

private noncomputable def compOfEq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (h : f ≫ g = fg) :
    Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
      Scheme.Modules.tensorPullback fg :=
  projectiveBundlePullbackComp f g ≪≫ projectiveBundlePullbackCongr h

private theorem compOfEq_assoc {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (fg : X ⟶ Z) (gh : Y ⟶ T) (fgh : X ⟶ T)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (h₁ : fg ≫ h = fgh) (h₂ : f ≫ gh = fgh) (M : T.Modules) :
    (compOfEq f g fg hfg).hom.app ((Scheme.Modules.tensorPullback h).obj M) ≫
        (compOfEq fg h fgh h₁).hom.app M =
      (Scheme.Modules.tensorPullback f).map ((compOfEq g h gh hgh).hom.app M) ≫
        (compOfEq f gh fgh h₂).hom.app M := by
  subst fg gh
  cases h₂
  have hh := NatTrans.congr_app (congrArg Iso.hom (comp_assoc f g h)) M
  simpa only [compOfEq, projectiveBundlePullbackCongr, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc,
    eqToIso.hom, eqToHom_refl, NatTrans.id_app] using hh

private theorem square_paste
    {W P' P U B : Scheme.{u}} (a : W ⟶ P') (j : P' ⟶ P) (q : P' ⟶ U)
    (p : P ⟶ B) (i : U ⟶ B) (k : W ⟶ P) (r : W ⟶ U)
    (hj : j ≫ p = q ≫ i) (ha : a ≫ j = k) (hr : a ≫ q = r)
    (hw : r ≫ i = k ≫ p) (E : B.Modules) :
    (Scheme.Modules.tensorPullback a).map
        ((compOfEq q i (j ≫ p) hj.symm).hom.app E ≫
          (projectiveBundlePullbackComp j p).inv.app E) ≫
        (compOfEq a j k ha).hom.app ((Scheme.Modules.tensorPullback p).obj E) =
      (compOfEq a q r hr).hom.app ((Scheme.Modules.tensorPullback i).obj E) ≫
        (compOfEq r i (k ≫ p) hw).hom.app E ≫
        (projectiveBundlePullbackComp k p).inv.app E := by
  have ht : a ≫ j ≫ p = k ≫ p := by rw [← Category.assoc, ha]
  have h₁ := compOfEq_assoc a q i r (j ≫ p) (k ≫ p) hr hj.symm hw ht E
  have h₂ : (compOfEq a j k ha).hom.app ((Scheme.Modules.tensorPullback p).obj E) ≫
      (projectiveBundlePullbackComp k p).hom.app E =
    (Scheme.Modules.tensorPullback a).map ((projectiveBundlePullbackComp j p).hom.app E) ≫
      (compOfEq a (j ≫ p) (k ≫ p) ht).hom.app E := by
    simpa only [compOfEq, projectiveBundlePullbackCongr, eqToIso_refl, Iso.trans_refl] using
      compOfEq_assoc a j p k (j ≫ p) (k ≫ p) ha rfl rfl ht E
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_mono ((projectiveBundlePullbackComp k p).hom.app E)).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [h₂]
  have hc : (Scheme.Modules.tensorPullback a).map
      ((projectiveBundlePullbackComp j p).inv.app E) ≫
      (Scheme.Modules.tensorPullback a).map
        ((projectiveBundlePullbackComp j p).hom.app E) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [reassoc_of% hc]
  exact h₁.symm

private theorem comp_picard {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) : (projectiveBundlePullbackComp f g).app M =
      Scheme.Modules.picardTensorCompIso f g M := by
  apply Iso.ext
  simp only [projectiveBundlePullbackComp, Scheme.Modules.picardTensorCompIso,
    projectiveBundleTensorPullbackIso, Scheme.Modules.picardTensorComparison,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]

private theorem unit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.tensorPullback f).map (projectiveBundlePullbackUnitIso g).hom ≫
        (projectiveBundlePullbackUnitIso f).hom =
      (projectiveBundlePullbackComp f g).hom.app (Scheme.Modules.unit Z) ≫
        (projectiveBundlePullbackUnitIso (f ≫ g)).hom := by
  rw [← Iso.app_hom, comp_picard]
  simpa only [projectiveBundlePullbackUnitIso, projectiveBundleTensorPullbackIso,
    Scheme.Modules.picardTensorUnitIso, Scheme.Modules.picardTensorComparison] using
    Scheme.Modules.picardTensorUnitIso_comp f g

private theorem unit_compOfEq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (h : f ≫ g = fg) :
    (projectiveBundlePullbackUnitIso f).inv ≫
        (Scheme.Modules.tensorPullback f).map (projectiveBundlePullbackUnitIso g).inv ≫
        (compOfEq f g fg h).hom.app (Scheme.Modules.unit Z) =
      (projectiveBundlePullbackUnitIso fg).inv := by
  subst fg
  have hu : (Scheme.Modules.tensorPullback f).mapIso (projectiveBundlePullbackUnitIso g) ≪≫
      projectiveBundlePullbackUnitIso f =
    (projectiveBundlePullbackComp f g).app (Scheme.Modules.unit Z) ≪≫
      projectiveBundlePullbackUnitIso (f ≫ g) := Iso.ext (unit_comp f g)
  have hi := congrArg Iso.inv hu
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at hi
  simp only [compOfEq, projectiveBundlePullbackCongr, eqToIso_refl, Iso.trans_refl]
  rw [← Category.assoc, hi, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem normalized_map_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg)
    {M : Z.Modules} (s : Scheme.Modules.unit Z ⟶ M) :
    (projectiveBundlePullbackUnitIso fg).inv ≫ (Scheme.Modules.tensorPullback fg).map s ≫
        (compOfEq f g fg h).inv.app M =
      (projectiveBundlePullbackUnitIso f).inv ≫ (Scheme.Modules.tensorPullback f).map
        ((projectiveBundlePullbackUnitIso g).inv ≫
          (Scheme.Modules.tensorPullback g).map s) := by
  apply (cancel_mono ((compOfEq f g fg h).hom.app M)).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.map_comp]
  have hn := (compOfEq f g fg h).hom.naturality s
  simp only [Functor.comp_map] at hn
  rw [hn]
  have hu := unit_compOfEq f g fg h
  simp only [← Category.assoc] at hu ⊢
  rw [hu]

private theorem paste_composites {C : Type*} [Category C]
    {A B D E F G H : C} (a₀ : A ⟶ B) (a₁ : B ⟶ D)
    (b₀ : A ⟶ E) (b₁ : E ⟶ F) (e : D ≅ F)
    (s : D ⟶ G) (t : G ⟶ H) (c : F ⟶ H)
    (h : a₀ ≫ a₁ = b₀ ≫ b₁ ≫ e.inv) (hp : s ≫ t = e.hom ≫ c) :
    a₀ ≫ a₁ ≫ s ≫ t = b₀ ≫ b₁ ≫ c := by
  rw [← Category.assoc a₀ a₁ (s ≫ t), h]
  simp only [Category.assoc, hp, Iso.inv_hom_id_assoc]

private theorem paste_nat_composites
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G) (M : C)
    {A B J K V : D} (a₀ : A ⟶ B) (a₁ : B ⟶ F.obj M)
    (b₀ : A ⟶ J) (b₁ : J ⟶ G.obj M)
    (s : F.obj M ⟶ K) (t : K ⟶ V) (c : G.obj M ⟶ V)
    (h : a₀ ≫ a₁ = b₀ ≫ b₁ ≫ e.inv.app M)
    (hp : s ≫ t = e.hom.app M ≫ c) :
    a₀ ≫ a₁ ≫ s ≫ t = b₀ ≫ b₁ ≫ c := by
  exact paste_composites a₀ a₁ b₀ b₁ (e.app M) s t c h hp

private theorem normalized_map_square
    {W P' P U B : Scheme.{u}} (a : W ⟶ P') (j : P' ⟶ P) (q : P' ⟶ U)
    (p : P ⟶ B) (i : U ⟶ B) (k : W ⟶ P) (r : W ⟶ U)
    (hj : j ≫ p = q ≫ i) (ha : a ≫ j = k) (hr : a ≫ q = r)
    (hw : r ≫ i = k ≫ p) (E : B.Modules)
    (s : Scheme.Modules.unit U ⟶ (Scheme.Modules.tensorPullback i).obj E) :
    (projectiveBundlePullbackUnitIso a).inv ≫ (Scheme.Modules.tensorPullback a).map
        ((projectiveBundlePullbackUnitIso q).inv ≫ (Scheme.Modules.tensorPullback q).map s) ≫
      (Scheme.Modules.tensorPullback a).map
        ((compOfEq q i (j ≫ p) hj.symm).hom.app E ≫
          (projectiveBundlePullbackComp j p).inv.app E) ≫
      (compOfEq a j k ha).hom.app ((Scheme.Modules.tensorPullback p).obj E) =
    (projectiveBundlePullbackUnitIso r).inv ≫ (Scheme.Modules.tensorPullback r).map s ≫
      (compOfEq r i (k ≫ p) hw).hom.app E ≫
      (projectiveBundlePullbackComp k p).inv.app E := by
  exact paste_nat_composites (compOfEq a q r hr)
    ((Scheme.Modules.tensorPullback i).obj E) _ _ _ _ _ _ _
    (normalized_map_comp a q r hr s).symm (square_paste a j q p i k r hj ha hr hw E)

private theorem comparison_section {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {U : Y.Opens} (m : Γ(M, U)) :
    ((projectiveBundleTensorPullbackIso g).app M).hom.app (g ⁻¹ᵁ U)
      (projectiveBundlePullbackSection g m) = Scheme.Modules.pullbackSection g m := by
  unfold projectiveBundleTensorPullbackIso projectiveBundlePullbackSection
    projectiveBundlePullbackAdjunction Scheme.Modules.Hom.app Scheme.Modules.pullbackSection
  exact congrArg (fun z ↦ z.val.app (op U) m)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g))
      (Scheme.Modules.pullbackPushforwardAdjunction g) M)

private theorem unit_comparison_section {X Y : Scheme.{u}} (g : X ⟶ Y)
    (U : Y.Opens) (r : Γ(Y, U)) :
    (projectiveBundlePullbackUnitIso g).hom.app (g ⁻¹ᵁ U)
      (projectiveBundlePullbackSection g (M := Scheme.Modules.unit Y) r) = g.app U r := by
  unfold projectiveBundlePullbackUnitIso
  change (Scheme.Modules.pullbackObjUnitIso g).hom.app _
    (((projectiveBundleTensorPullbackIso g).app _).hom.app _
      (projectiveBundlePullbackSection g r)) = _
  rw [comparison_section, Scheme.Modules.pullbackObjUnitIso_hom_app_pullbackSection]

private theorem section_of_unit_equation {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {P : X.Modules} (a : Scheme.Modules.unit Y ⟶ M)
    (t : (Scheme.Modules.tensorPullback g).obj M ⟶ P) (b : Scheme.Modules.unit X ⟶ P)
    (h : (Scheme.Modules.tensorPullback g).map a ≫ t =
      (projectiveBundlePullbackUnitIso g).hom ≫ b) :
    t.app (g ⁻¹ᵁ ⊤) (projectiveBundlePullbackSection g (a.app ⊤ (1 : Γ(Y, ⊤)))) =
      b.app (g ⁻¹ᵁ ⊤) (1 : Γ(X, g ⁻¹ᵁ ⊤)) := by
  have hn := congrArg (fun z ↦ z.app ⊤ (1 : Γ(Y, ⊤)))
    ((projectiveBundlePullbackAdjunction g).unit.naturality a)
  have he := congrArg (fun z ↦ z.app (g ⁻¹ᵁ ⊤)
    (projectiveBundlePullbackSection g (M := Scheme.Modules.unit Y) (1 : Γ(Y, ⊤)))) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Functor.id_map, Functor.comp_map, ConcreteCategory.comp_apply] at hn he
  rw [unit_comparison_section, map_one] at he
  unfold projectiveBundlePullbackSection at he ⊢
  exact (congrArg (t.app (g ⁻¹ᵁ ⊤)) hn).trans he

private theorem section_of_unit_equation_global {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {P : X.Modules} (a : Scheme.Modules.unit Y ⟶ M) (m : Γ(M, ⊤))
    (hm : a.app ⊤ (1 : Γ(Y, ⊤)) = m)
    (t : (Scheme.Modules.tensorPullback g).obj M ⟶ P) (b : Scheme.Modules.unit X ⟶ P)
    (h : (Scheme.Modules.tensorPullback g).map a ≫ t =
      (projectiveBundlePullbackUnitIso g).hom ≫ b) :
    t.app (g ⁻¹ᵁ ⊤) (projectiveBundlePullbackSection g m) =
      b.app (g ⁻¹ᵁ ⊤) (1 : Γ(X, g ⁻¹ᵁ ⊤)) := by
  rw [← hm]
  exact section_of_unit_equation g a t b h

private theorem unitMap_app_one {X : Scheme.{u}} {M : X.Modules}
    (b : Scheme.Modules.unit X ⟶ M) (V : X.Opens) :
    b.app V (1 : Γ(X, V)) =
      M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (b.app ⊤ (1 : Γ(X, ⊤))) := by
  rw [← Scheme.Modules.Hom.app_presheaf_map]
  congr 1
  change (1 : Γ(X, V)) =
    (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (1 : Γ(X, ⊤))
  exact (map_one (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom).symm

private theorem pullbackCongr_app {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) :
    (projectiveBundlePullbackCongr h).hom.app M =
      (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj M) h)).hom := by
  subst h
  simp [projectiveBundlePullbackCongr]

private theorem comp_transport_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (h : f ≫ g = fg) (M : Z.Modules) :
    (projectiveBundlePullbackComp f g ≪≫ projectiveBundlePullbackCongr h).hom.app M =
      (Scheme.Modules.tensorPullbackSectionComp f g).inv.app M ≫
        (eqToIso (congrArg (fun v ↦ (Scheme.Modules.tensorPullback v).obj M) h)).hom := by
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [comp_comparison_eq]
  simp only [Iso.symm_hom, pullbackCongr_app]

private theorem comp_components_transport_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg) (M : Z.Modules) :
    ((projectiveBundlePullbackComp f g).app M ≪≫
      (projectiveBundlePullbackCongr h).app M).hom =
      (Scheme.Modules.tensorPullbackSectionComp f g).inv.app M ≫
        (eqToIso (congrArg (fun v ↦ (Scheme.Modules.tensorPullback v).obj M) h)).hom := by
  rw [← NatIso.trans_app]
  exact comp_transport_hom f g fg h M

private theorem unit_boundary {X Y : Scheme.{u}} (g : X ⟶ Y) :
    projectiveBundlePullbackUnitIso g =
      (Scheme.Modules.boundaryPullbackComparison g).app (Scheme.Modules.unit Y) ≪≫
        Scheme.Modules.pullbackObjUnitIso g := by
  unfold projectiveBundlePullbackUnitIso projectiveBundleTensorPullbackIso
    Scheme.Modules.boundaryPullbackComparison
  rfl

private theorem normalize_quotient_square
    {P' P U B : Scheme.{u}} (j : P' ⟶ P) (q : P' ⟶ U) (p : P ⟶ B)
    (i : U ⟶ B) (hj : j ≫ p = q ≫ i) (E : B.Modules) (L : P.Modules)
    (L' : P'.Modules) (qp : (Scheme.Modules.tensorPullback p).obj E ⟶ L)
    (qu : (Scheme.Modules.tensorPullback q).obj
      ((Scheme.Modules.tensorPullback i).obj E) ⟶ L')
    (w : (Scheme.Modules.tensorPullback j).obj L ≅ L')
    (h : (Scheme.Modules.tensorPullbackSectionComp j p).hom.app E ≫
        (Scheme.Modules.tensorPullback j).map qp ≫ w.hom =
      (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj E) hj)).hom ≫
        (Scheme.Modules.tensorPullbackSectionComp q i).hom.app E ≫ qu) :
    (projectiveBundlePullbackComp j p).inv.app E ≫
        (Scheme.Modules.tensorPullback j).map qp ≫ w.hom =
      (projectiveBundlePullbackCongr hj).hom.app E ≫
        (projectiveBundlePullbackComp q i).inv.app E ≫ qu := by
  simpa only [comp_comparison_eq, Iso.symm_inv, pullbackCongr_app] using h

private theorem normalize_free_coordinate
    {X S Z : Scheme.{u}} (q : X ⟶ S) (z : X ⟶ Z) (E : S.Modules)
    (L : X.Modules) (T : Z.Modules) (qu : (Scheme.Modules.tensorPullback q).obj E ⟶ L)
    (t : (Scheme.Modules.tensorPullback z).obj T ≅ L)
    (basis : Scheme.Modules.unit S ⟶ E) (coord : Scheme.Modules.unit Z ⟶ T)
    (h : (Scheme.Modules.tensorPullback q).map basis ≫ qu =
      ((Scheme.Modules.boundaryPullbackComparison q).app (Scheme.Modules.unit S) ≪≫
        Scheme.Modules.pullbackObjUnitIso q).hom ≫
      ((Scheme.Modules.boundaryPullbackComparison z).app (Scheme.Modules.unit Z) ≪≫
        Scheme.Modules.pullbackObjUnitIso z).inv ≫
      (Scheme.Modules.tensorPullback z).map coord ≫ t.hom) :
    (Scheme.Modules.tensorPullback q).map basis ≫ qu =
      (projectiveBundlePullbackUnitIso q).hom ≫
        (projectiveBundlePullbackUnitIso z).inv ≫
        (Scheme.Modules.tensorPullback z).map coord ≫ t.hom := by
  simpa only [unit_boundary, Iso.symm_hom] using h

private theorem coordinate_transport
    {W P' P U B Z : Scheme.{u}} (a : W ⟶ P') (j : P' ⟶ P) (q : P' ⟶ U)
    (p : P ⟶ B) (i : U ⟶ B) (k : W ⟶ P) (r : W ⟶ U)
    (z : P' ⟶ Z) (φ : W ⟶ Z)
    (hj : j ≫ p = q ≫ i) (ha : a ≫ j = k) (hr : a ≫ q = r)
    (hw : r ≫ i = k ≫ p) (hz : a ≫ z = φ)
    (E : B.Modules) (L : P.Modules) (L' : P'.Modules) (T : Z.Modules)
    (qp : (Scheme.Modules.tensorPullback p).obj E ⟶ L)
    (qu : (Scheme.Modules.tensorPullback q).obj
      ((Scheme.Modules.tensorPullback i).obj E) ⟶ L')
    (w : (Scheme.Modules.tensorPullback j).obj L ≅ L')
    (t : (Scheme.Modules.tensorPullback z).obj T ≅ L')
    (basis : Scheme.Modules.unit U ⟶ (Scheme.Modules.tensorPullback i).obj E)
    (coord : Scheme.Modules.unit Z ⟶ T)
    (hopen : (projectiveBundlePullbackComp j p).inv.app E ≫
        (Scheme.Modules.tensorPullback j).map qp ≫ w.hom =
      (projectiveBundlePullbackCongr hj).hom.app E ≫
        (projectiveBundlePullbackComp q i).inv.app E ≫ qu)
    (hfree : (Scheme.Modules.tensorPullback q).map basis ≫ qu =
      (projectiveBundlePullbackUnitIso q).hom ≫
        (projectiveBundlePullbackUnitIso z).inv ≫
        (Scheme.Modules.tensorPullback z).map coord ≫ t.hom) :
    (projectiveBundlePullbackUnitIso φ).inv ≫
        (Scheme.Modules.tensorPullback φ).map coord ≫
        (compOfEq a z φ hz).inv.app T ≫
        (Scheme.Modules.tensorPullback a).map t.hom ≫
        (Scheme.Modules.tensorPullback a).map w.inv ≫
        (compOfEq a j k ha).hom.app L =
      (projectiveBundlePullbackUnitIso r).inv ≫
        (Scheme.Modules.tensorPullback r).map basis ≫
        (compOfEq r i (k ≫ p) hw).hom.app E ≫
        (projectiveBundlePullbackComp k p).inv.app E ≫
        (Scheme.Modules.tensorPullback k).map qp := by
  let S := (compOfEq q i (j ≫ p) hj.symm).app E ≪≫
    ((projectiveBundlePullbackComp j p).app E).symm
  have ho : qu ≫ w.inv = S.hom ≫ (Scheme.Modules.tensorPullback j).map qp := by
    apply (cancel_mono w.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [S, compOfEq, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      NatTrans.comp_app]
    simp only [Category.assoc]
    rw [hopen]
    simp [projectiveBundlePullbackCongr]
  have hf : (projectiveBundlePullbackUnitIso z).inv ≫
      (Scheme.Modules.tensorPullback z).map coord ≫ t.hom =
    (projectiveBundlePullbackUnitIso q).inv ≫
      (Scheme.Modules.tensorPullback q).map basis ≫ qu := by
    rw [hfree, Iso.inv_hom_id_assoc]
  rw [reassoc_of% (normalized_map_comp a z φ hz coord)]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  rw [reassoc_of% hf, ho]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (compOfEq a j k ha).hom.naturality qp
  simp only [Functor.comp_map] at hn
  rw [hn]
  have hs := normalized_map_square a j q p i k r hj ha hr hw E basis
  simpa only [S, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc, Functor.map_comp] using
    congrArg (fun v ↦ v ≫ (Scheme.Modules.tensorPullback k).map qp) hs

private theorem normalized_chart_overlap {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg)
    (L : Z.Modules) (M : Y.Modules) (N : X.Modules)
    (a : (Scheme.Modules.tensorPullback g).obj L ≅ M)
    (b : (Scheme.Modules.tensorPullback fg).obj L ≅ N)
    (c : (Scheme.Modules.tensorPullback f).obj M ≅ N)
    (hc : (Scheme.Modules.tensorPullback f).map a.hom ≫ c.hom =
      (Scheme.Modules.tensorPullbackSectionComp f g).inv.app L ≫
        (eqToIso (congrArg (fun v ↦ (Scheme.Modules.tensorPullback v).obj L) h)).hom ≫
          b.hom) :
    ((projectiveBundlePullbackComp f g).app L ≪≫
      (projectiveBundlePullbackCongr h).app L) ≪≫ b =
        (Scheme.Modules.tensorPullback f).mapIso a ≪≫ c := by
  apply Iso.ext
  change ((projectiveBundlePullbackComp f g).app L ≪≫
    (projectiveBundlePullbackCongr h).app L).hom ≫ b.hom =
      (Scheme.Modules.tensorPullback f).map a.hom ≫ c.hom
  rw [comp_components_transport_hom]
  simpa only [Category.assoc] using hc.symm

private noncomputable def twistsOfQuotient {B : Scheme.{u}} (F : B.Modules)
    [F.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient F)
    (c : ∀ (U V : B.affineOpens) (h : U ≤ V),
      SymmetricProjTautologicalCharts.NormalizedAffineRestriction F D U V h) :
    TautologicalTwistData B (SymmetricAlgebraSheaf.gradedAlgebraData F) D.line where
  chart := D.chart
  twistRestriction := fun {U V} h ↦ (c U V h).comparison
  restriction_generator := by
    intro U V h x hx
    apply section_of_unit_equation _ (Proj.unitToTwist hx)
    simpa only [unit_boundary, Scheme.GradedAlgebraData.relProjFunctor_obj] using
      (c U V h).section_compatibility x hx
  chart_overlap := fun {U V} h ↦ normalized_chart_overlap
    ((SymmetricAlgebraSheaf.gradedAlgebraData F).relProjFunctor.map (homOfLE h))
    ((SymmetricAlgebraSheaf.gradedAlgebraData F).relProjι V)
    ((SymmetricAlgebraSheaf.gradedAlgebraData F).relProjι U)
    ((SymmetricAlgebraSheaf.gradedAlgebraData F).relProjFunctor_map_relProjι (homOfLE h))
    D.line _ _ (D.chart V) (D.chart U) (c U V h).comparison
    (c U V h).chart_compatibility

private noncomputable def realizationOfQuotient {B : Scheme.{u}} (F : B.Modules)
    [F.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient F)
    (c : ∀ (U V : B.affineOpens) (h : U ≤ V),
      SymmetricProjTautologicalCharts.NormalizedAffineRestriction F D U V h) :
    ProjectiveBundleRealization B F where
  A := symmetricData F
  L := D.line
  quotient := D.quotient
  twists := twistsOfQuotient F D c
  quotient_generator := by
    intro U x hx
    change (D.chart U).hom.app _ (projectiveBundlePullbackSection _
      (((projectiveBundlePullbackAdjunction _).homEquiv F D.line D.quotient).app U.1 x)) = _
    rw [normalized_adjunction_eq, normalized_section_eq]
    exact D.generator U x hx

private noncomputable def chartOfCoordinates {B : Scheme.{u}} {F : B.Modules}
    (D : ProjectiveBundleRealization B F) (n : ℕ) (U : B.Opens)
    (e : B.ModuleFrame F U (n + 1))
    (c : (D.A.data.relProjHom ⁻¹ᵁ U).toScheme ≅ RelativeProjectiveSpace.scheme U.toScheme n)
    (hc : c.hom ≫ RelativeProjectiveSpace.π U.toScheme n = D.A.data.relProjHom ∣_ U)
    (d : RelativeProjectiveSpace.scheme U.toScheme n ≅
      ℙ(ULift.{u} (Fin (n + 1)); U.toScheme))
    (hd : d.hom ≫ (ℙ(ULift.{u} (Fin (n + 1)); U.toScheme) ↘ U.toScheme) =
      RelativeProjectiveSpace.π U.toScheme n)
    (t : (Scheme.Modules.tensorPullback (c.hom ≫ d.hom)).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) U.toScheme 1) ≅
      (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj D.L)
    (ht : ∀ i : ULift.{u} (Fin (n + 1)),
      (projectiveBundlePullbackUnitIso (c.hom ≫ d.hom)).inv ≫
        (Scheme.Modules.tensorPullback (c.hom ≫ d.hom)).map
          (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (n + 1))) U.toScheme i) ≫
        t.hom = projectiveBundleFrameSection D n U e i) : ProjectiveBundleFrameChart D n U e := by
  let X := (D.A.data.relProjHom ⁻¹ᵁ U).toScheme
  let M := (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj D.L
  let φ := c.hom ≫ d.hom
  let T := ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) U.toScheme 1
  let s : ULift.{u} (Fin (n + 1)) → Γ(M, ⊤) := fun j ↦
    (projectiveBundleFrameSection D n U e j).app ⊤ (1 : Γ(X, ⊤))
  let b : ProjectiveSpace.twistRestrict φ 1 ≅ M :=
    ((projectiveBundleTensorPullbackIso φ).app T).symm ≪≫ t
  have hb : ∀ j, b.hom.app (φ ⁻¹ᵁ ⊤)
      (Scheme.Modules.pullbackSection φ
        (ProjectiveSpace.twistOneSection (ULift.{u} (Fin (n + 1))) U.toScheme j)) =
      M.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ ⊤ ≤ ⊤)).op (s j) := by
    intro j
    have hcomp := comparison_section φ
      (ProjectiveSpace.twistOneSection (ULift.{u} (Fin (n + 1))) U.toScheme j)
    rw [← hcomp]
    change t.hom.app _
      ((((projectiveBundleTensorPullbackIso φ).app T).hom ≫
        ((projectiveBundleTensorPullbackIso φ).app T).inv).app _
        (projectiveBundlePullbackSection φ _)) = _
    simp only [Iso.hom_inv_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
    have h := section_of_unit_equation_global φ
      (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (n + 1))) U.toScheme j)
      (ProjectiveSpace.twistOneSection (ULift.{u} (Fin (n + 1))) U.toScheme j)
      (ProjectiveSpace.coordinateSection_app_top_one _ _ j) t.hom
      (projectiveBundleFrameSection D n U e j) (by
        dsimp only [φ]
        rw [← ht j]
        simp only [Iso.hom_inv_id_assoc])
    exact h.trans (unitMap_app_one (projectiveBundleFrameSection D n U e j) _)
  exact {
    relativeChart := c
    relativeChart_over := hc
    polynomialChart := d
    polynomialChart_over := hd
    twist := t
    coordinate := ht
    generator := fun i ↦ ProjectiveSpace.isFreeGenerator_of_twistRestrict_iso
      (X := X) (S := U.toScheme) (n := ULift.{u} (Fin (n + 1)))
      (M := M) (s := s) (φ := φ) b.hom hb i
    transition := fun i j ↦ ProjectiveSpace.map_eq_coordRatio_smul_of_twistRestrict_iso
      (X := X) (S := U.toScheme) (n := ULift.{u} (Fin (n + 1)))
      (M := M) (s := s) (φ := φ) b.hom hb j i }

private theorem compOfEq_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (h : f ≫ g = fg) (M : Z.Modules) :
    (compOfEq f g fg h).app M =
      (projectiveBundlePullbackComp f g).app M ≪≫
        (projectiveBundlePullbackCongr h).app M := by
  exact NatIso.trans_app (projectiveBundlePullbackComp f g) (projectiveBundlePullbackCongr h) M

private theorem coordinate_transport_components
    {W P' P U B Z : Scheme.{u}} (a : W ⟶ P') (j : P' ⟶ P) (q : P' ⟶ U)
    (p : P ⟶ B) (i : U ⟶ B) (k : W ⟶ P) (r : W ⟶ U)
    (z : P' ⟶ Z) (φ : W ⟶ Z)
    (hj : j ≫ p = q ≫ i) (ha : a ≫ j = k) (hr : a ≫ q = r)
    (hw : r ≫ i = k ≫ p) (hz : a ≫ z = φ)
    (E : B.Modules) (L : P.Modules) (L' : P'.Modules) (T : Z.Modules)
    (qp : (Scheme.Modules.tensorPullback p).obj E ⟶ L)
    (qu : (Scheme.Modules.tensorPullback q).obj
      ((Scheme.Modules.tensorPullback i).obj E) ⟶ L')
    (w : (Scheme.Modules.tensorPullback j).obj L ≅ L')
    (t : (Scheme.Modules.tensorPullback z).obj T ≅ L')
    (basis : Scheme.Modules.unit U ⟶ (Scheme.Modules.tensorPullback i).obj E)
    (coord : Scheme.Modules.unit Z ⟶ T)
    (hopen : (projectiveBundlePullbackComp j p).inv.app E ≫
        (Scheme.Modules.tensorPullback j).map qp ≫ w.hom =
      (projectiveBundlePullbackCongr hj).hom.app E ≫
        (projectiveBundlePullbackComp q i).inv.app E ≫ qu)
    (hfree : (Scheme.Modules.tensorPullback q).map basis ≫ qu =
      (projectiveBundlePullbackUnitIso q).hom ≫
        (projectiveBundlePullbackUnitIso z).inv ≫
        (Scheme.Modules.tensorPullback z).map coord ≫ t.hom) :
    (projectiveBundlePullbackUnitIso φ).inv ≫
        (Scheme.Modules.tensorPullback φ).map coord ≫
        ((projectiveBundlePullbackComp a z).app T ≪≫
          (projectiveBundlePullbackCongr hz).app T).inv ≫
        (Scheme.Modules.tensorPullback a).map t.hom ≫
        (Scheme.Modules.tensorPullback a).map w.inv ≫
        ((projectiveBundlePullbackComp a j).app L ≪≫
          (projectiveBundlePullbackCongr ha).app L).hom =
      (projectiveBundlePullbackUnitIso r).inv ≫
        (Scheme.Modules.tensorPullback r).map basis ≫
        ((projectiveBundlePullbackComp r i).app E ≪≫
          (projectiveBundlePullbackCongr hw).app E).hom ≫
        ((projectiveBundlePullbackComp k p).app E).inv ≫
        (Scheme.Modules.tensorPullback k).map qp := by
  have ht := coordinate_transport a j q p i k r z φ hj ha hr hw hz
    E L L' T qp qu w t basis coord hopen hfree
  rw [← Iso.app_inv (compOfEq a z φ hz) T, compOfEq_app] at ht
  rw [← Iso.app_hom (compOfEq a j k ha) L, compOfEq_app] at ht
  rw [← Iso.app_hom (compOfEq r i (k ≫ p) hw) E, compOfEq_app] at ht
  rw [← Iso.app_inv (projectiveBundlePullbackComp k p) E] at ht
  exact ht

private theorem iso_coordinate_paste
    {C D : Type*} [Category C] [Category D] (K : C ⥤ D)
    {A B C' : C} {P Q S H U X Y V W : D}
    (a : K.obj A ≅ P) (t : A ≅ B) (w : C' ≅ B) (d : K.obj C' ≅ Q)
    (c : X ≅ Y) (v : Y ≅ V) (r : W ≅ V)
    (s₀ : U ⟶ S) (s₁ : S ⟶ P) (b₀ : U ⟶ H) (b₁ : H ⟶ X) (qp : W ⟶ Q)
    (h : s₀ ≫ s₁ ≫ a.inv ≫ K.map t.hom ≫ K.map w.inv ≫ d.hom =
      b₀ ≫ b₁ ≫ (c ≪≫ v).hom ≫ r.inv ≫ qp) :
    s₀ ≫ s₁ ≫ (a.symm ≪≫ K.mapIso t ≪≫ K.mapIso w.symm ≪≫ d).hom =
      (b₀ ≫ b₁ ≫ c.hom ≫ v.hom ≫ r.inv) ≫ qp := by
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using h

private noncomputable def coordinateTwistIso
    {W P' P Z : Scheme.{u}} (a : W ⟶ P') (j : P' ⟶ P) (k : W ⟶ P)
    (z : P' ⟶ Z) (φ : W ⟶ Z) (ha : a ≫ j = k) (hz : a ≫ z = φ)
    (L : P.Modules) (L' : P'.Modules) (T : Z.Modules)
    (w : (Scheme.Modules.tensorPullback j).obj L ≅ L')
    (t : (Scheme.Modules.tensorPullback z).obj T ≅ L') :
    (Scheme.Modules.tensorPullback φ).obj T ≅ (Scheme.Modules.tensorPullback k).obj L :=
  ((projectiveBundlePullbackComp a z).app T ≪≫
    (projectiveBundlePullbackCongr hz).app T).symm ≪≫
    (Scheme.Modules.tensorPullback a).mapIso t ≪≫
    (Scheme.Modules.tensorPullback a).mapIso w.symm ≪≫
    (projectiveBundlePullbackComp a j).app L ≪≫
      (projectiveBundlePullbackCongr ha).app L

private theorem coordinate_transport_iso
    {W P' P U B Z : Scheme.{u}} (a : W ⟶ P') (j : P' ⟶ P) (q : P' ⟶ U)
    (p : P ⟶ B) (i : U ⟶ B) (k : W ⟶ P) (r : W ⟶ U)
    (z : P' ⟶ Z) (φ : W ⟶ Z)
    (hj : j ≫ p = q ≫ i) (ha : a ≫ j = k) (hr : a ≫ q = r)
    (hw : r ≫ i = k ≫ p) (hz : a ≫ z = φ)
    (E : B.Modules) (L : P.Modules) (L' : P'.Modules) (T : Z.Modules)
    (qp : (Scheme.Modules.tensorPullback p).obj E ⟶ L)
    (qu : (Scheme.Modules.tensorPullback q).obj
      ((Scheme.Modules.tensorPullback i).obj E) ⟶ L')
    (w : (Scheme.Modules.tensorPullback j).obj L ≅ L')
    (t : (Scheme.Modules.tensorPullback z).obj T ≅ L')
    (basis : Scheme.Modules.unit U ⟶ (Scheme.Modules.tensorPullback i).obj E)
    (coord : Scheme.Modules.unit Z ⟶ T)
    (hopen : (projectiveBundlePullbackComp j p).inv.app E ≫
        (Scheme.Modules.tensorPullback j).map qp ≫ w.hom =
      (projectiveBundlePullbackCongr hj).hom.app E ≫
        (projectiveBundlePullbackComp q i).inv.app E ≫ qu)
    (hfree : (Scheme.Modules.tensorPullback q).map basis ≫ qu =
      (projectiveBundlePullbackUnitIso q).hom ≫
        (projectiveBundlePullbackUnitIso z).inv ≫
        (Scheme.Modules.tensorPullback z).map coord ≫ t.hom) :
    (projectiveBundlePullbackUnitIso φ).inv ≫
        (Scheme.Modules.tensorPullback φ).map coord ≫
        (coordinateTwistIso a j k z φ ha hz L L' T w t).hom =
      ((projectiveBundlePullbackUnitIso r).inv ≫
        (Scheme.Modules.tensorPullback r).map basis ≫
        ((projectiveBundlePullbackComp r i).app E).hom ≫
        (projectiveBundlePullbackCongr hw).hom.app E ≫
        ((projectiveBundlePullbackComp k p).app E).inv) ≫
        (Scheme.Modules.tensorPullback k).map qp := by
  unfold coordinateTwistIso
  rw [← Iso.app_hom (projectiveBundlePullbackCongr hw) E]
  have ht := coordinate_transport_components a j q p i k r z φ hj ha hr hw hz
    E L L' T qp qu w t basis coord hopen hfree
  exact iso_coordinate_paste (Scheme.Modules.tensorPullback a)
    ((projectiveBundlePullbackComp a z).app T ≪≫ (projectiveBundlePullbackCongr hz).app T)
    t w ((projectiveBundlePullbackComp a j).app L ≪≫
      (projectiveBundlePullbackCongr ha).app L)
    ((projectiveBundlePullbackComp r i).app E) ((projectiveBundlePullbackCongr hw).app E)
    ((projectiveBundlePullbackComp k p).app E)
    (projectiveBundlePullbackUnitIso φ).inv ((Scheme.Modules.tensorPullback φ).map coord)
    (projectiveBundlePullbackUnitIso r).inv ((Scheme.Modules.tensorPullback r).map basis)
    ((Scheme.Modules.tensorPullback k).map qp) ht

private theorem frameChartOfGivenComparison {B : Scheme.{u}} {F : B.Modules}
    (R : ProjectiveBundleRealization B F) (n : ℕ) (U : B.Opens)
    (e : B.ModuleFrame F U (n + 1)) {P' : Scheme.{u}} (q : P' ⟶ U.toScheme)
    (L' : P'.Modules)
    (qu : (Scheme.Modules.tensorPullback q).obj
      ((Scheme.Modules.tensorPullback U.ι).obj F) ⟶ L')
    (j : P' ⟶ R.A.data.relProj) (hj : j ≫ R.A.data.relProjHom = q ≫ U.ι)
    (a : (R.A.data.relProjHom ⁻¹ᵁ U).toScheme ≅ P')
    (ha : a.hom ≫ j = (R.A.data.relProjHom ⁻¹ᵁ U).ι)
    (hr : a.hom ≫ q = R.A.data.relProjHom ∣_ U)
    (w : (Scheme.Modules.tensorPullback j).obj R.L ≅ L')
    (hopen : (projectiveBundlePullbackComp j R.A.data.relProjHom).inv.app F ≫
        (Scheme.Modules.tensorPullback j).map R.quotient ≫ w.hom =
      (projectiveBundlePullbackCongr hj).hom.app F ≫
        (projectiveBundlePullbackComp q U.ι).inv.app F ≫ qu)
    (eRel : P' ≅ RelativeProjectiveSpace.scheme U.toScheme n)
    (eStd : P' ≅ ℙ(ULift.{u} (Fin (n + 1)); U.toScheme))
    (tU : (Scheme.Modules.tensorPullback eStd.hom).obj
      (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) U.toScheme 1) ≅ L')
    (hRel : eRel.hom ≫ RelativeProjectiveSpace.π U.toScheme n = q)
    (hStd : eStd.hom ≫ (ℙ(ULift.{u} (Fin (n + 1)); U.toScheme) ↘ U.toScheme) = q)
    (hcoord : ∀ l : ULift.{u} (Fin (n + 1)),
      (Scheme.Modules.tensorPullback q).map
        (SheafOfModules.ιFree (R := U.toScheme.ringCatSheaf) l ≫ e.inv) ≫ qu =
      (projectiveBundlePullbackUnitIso q).hom ≫
        (projectiveBundlePullbackUnitIso eStd.hom).inv ≫
        (Scheme.Modules.tensorPullback eStd.hom).map
          (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (n + 1))) U.toScheme l) ≫
        tU.hom) : Nonempty (ProjectiveBundleFrameChart R n U e) := by
  classical
  let cU := a ≪≫ eRel
  let dU := eRel.symm ≪≫ eStd
  have hc : cU.hom ≫ RelativeProjectiveSpace.π U.toScheme n = (R.A.data.relProjHom ∣_ U) := by
    change (a.hom ≫ eRel.hom) ≫ _ = _
    rw [Category.assoc, hRel, hr]
  have hd : dU.hom ≫ (ℙ(ULift.{u} (Fin (n + 1)); U.toScheme) ↘ U.toScheme) =
      RelativeProjectiveSpace.π U.toScheme n := by
    change (eRel.inv ≫ eStd.hom) ≫ _ = _
    rw [Category.assoc, hStd, ← hRel, ← Category.assoc,
      eRel.inv_hom_id, Category.id_comp]
  have hz : a.hom ≫ eStd.hom = (cU.hom ≫ dU.hom) := by
    simp [cU, dU, Category.assoc]
  let t : (Scheme.Modules.tensorPullback (cU.hom ≫ dU.hom)).obj
      (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) U.toScheme 1) ≅
      (Scheme.Modules.tensorPullback (R.A.data.relProjHom ⁻¹ᵁ U).ι).obj R.L :=
    coordinateTwistIso a.hom j (R.A.data.relProjHom ⁻¹ᵁ U).ι eStd.hom
      (cU.hom ≫ dU.hom) ha hz R.L L'
      (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) U.toScheme 1) w tU
  refine ⟨chartOfCoordinates R n U e cU hc dU hd t ?_⟩
  intro l
  have ht := coordinate_transport_iso a.hom j q R.A.data.relProjHom U.ι
    (R.A.data.relProjHom ⁻¹ᵁ U).ι (R.A.data.relProjHom ∣_ U) eStd.hom (cU.hom ≫ dU.hom)
    hj ha hr (morphismRestrict_ι R.A.data.relProjHom U) hz F R.L L'
    (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) U.toScheme 1) R.quotient qu
    w tU (SheafOfModules.ιFree (R := U.toScheme.ringCatSheaf) l ≫ e.inv)
    (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (n + 1))) U.toScheme l) hopen (hcoord l)
  exact ht.trans (projectiveBundleFrameSection_formula R n U e l).symm

private theorem normalized_free_comparison {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (n : ℕ) (e : E ≅ RelativeProjectiveSpace.freeModule S n) :
    ∃ (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
        RelativeProjectiveSpace.scheme S n)
      (eStd : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
        ℙ(ULift.{u} (Fin (n + 1)); S))
      (t : (Scheme.Modules.tensorPullback eStd.hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) S 1) ≅ D.line),
      (eRel.hom ≫ RelativeProjectiveSpace.π S n =
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) ∧
      (eStd.hom ≫ (ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S) =
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) ∧
      ∀ i : ULift.{u} (Fin (n + 1)),
        (Scheme.Modules.tensorPullback
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
          (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ e.inv) ≫ D.quotient =
        (projectiveBundlePullbackUnitIso
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
        (projectiveBundlePullbackUnitIso eStd.hom).inv ≫
        (Scheme.Modules.tensorPullback eStd.hom).map
          (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (n + 1))) S i) ≫ t.hom := by
  obtain ⟨eRel, eStd, t, hRel, hStd, hcoord, _⟩ :=
    SymmetricProjTautologicalCharts.free_compatibility_of_normalized_quotient S E D n e.symm
  refine ⟨eRel, eStd, t, hRel, hStd, ?_⟩
  intro i
  have hc := hcoord i
  rw [Iso.symm_hom] at hc
  exact normalize_free_coordinate (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
    eStd.hom E D.line _ D.quotient t
    (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ e.inv)
    (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (n + 1))) S i) hc

private theorem exists_restricted_pullback_iso
    {B P P' : Scheme.{u}} (p : P ⟶ B) (U : B.Opens)
    (q : P' ⟶ U.toScheme) (j : P' ⟶ P) (hj : IsPullback j q p U.ι) :
    ∃ a : (p ⁻¹ᵁ U).toScheme ≅ P',
      a.hom ≫ j = (p ⁻¹ᵁ U).ι ∧ a.hom ≫ q = p ∣_ U := by
  refine ⟨(hj.isoIsPullback _ _ (isPullback_morphismRestrict p U).flip).symm, ?_, ?_⟩
  · exact hj.isoIsPullback_inv_fst _ _ (isPullback_morphismRestrict p U).flip
  · exact hj.isoIsPullback_inv_snd _ _ (isPullback_morphismRestrict p U).flip

-- Packaging the diagram lets congruence transport its equation before specialization.

private structure QuotientDiagram
    {P' U B : Scheme.{u}} (q : P' ⟶ U) (i : U ⟶ B)
    (E : B.Modules) (L' : P'.Modules) where
  P : Scheme.{u}
  j : P' ⟶ P
  p : P ⟶ B
  L : P.Modules
  quotient : (Scheme.Modules.tensorPullback p).obj E ⟶ L
  over : j ≫ p = q ≫ i
  line : (Scheme.Modules.tensorPullback j).obj L ≅ L'

private def quotientDiagramCondition
    {P' U B : Scheme.{u}} {q : P' ⟶ U} {i : U ⟶ B}
    {E : B.Modules} {L' : P'.Modules}
    (qu : (Scheme.Modules.tensorPullback q).obj
      ((Scheme.Modules.tensorPullback i).obj E) ⟶ L') :
    QuotientDiagram q i E L' → Prop
  | ⟨_, j, p, _, qp, hj, w⟩ =>
    (projectiveBundlePullbackComp j p).inv.app E ≫
        (Scheme.Modules.tensorPullback j).map qp ≫ w.hom =
      (projectiveBundlePullbackCongr hj).hom.app E ≫
        (projectiveBundlePullbackComp q i).inv.app E ≫ qu

private theorem realizationDiagram_eq {B : Scheme.{u}} (F : B.Modules) [F.IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient F)
    (c : ∀ (U V : B.affineOpens) (h : U ≤ V),
      SymmetricProjTautologicalCharts.NormalizedAffineRestriction F D U V h)
    (U : B.Opens) {P' : Scheme.{u}} (q : P' ⟶ U.toScheme) (L' : P'.Modules)
    (j : P' ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData F).relProj)
    (hj : j ≫ (SymmetricAlgebraSheaf.gradedAlgebraData F).relProjHom = q ≫ U.ι)
    (w : (Scheme.Modules.tensorPullback j).obj D.line ≅ L') :
    (⟨(SymmetricAlgebraSheaf.gradedAlgebraData F).relProj, j,
      (SymmetricAlgebraSheaf.gradedAlgebraData F).relProjHom,
      D.line, D.quotient, hj, w⟩ : QuotientDiagram q U.ι F L') =
    (⟨(realizationOfQuotient F D c).A.data.relProj, j,
      (realizationOfQuotient F D c).A.data.relProjHom,
      (realizationOfQuotient F D c).L, (realizationOfQuotient F D c).quotient, hj, w⟩ :
      QuotientDiagram q U.ι F L') := by rfl

private theorem realization_quotient_square {B : Scheme.{u}} (F : B.Modules) [F.IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient F)
    (c : ∀ (U V : B.affineOpens) (h : U ≤ V),
      SymmetricProjTautologicalCharts.NormalizedAffineRestriction F D U V h)
    (U : B.Opens) {P' : Scheme.{u}} (q : P' ⟶ U.toScheme) (L' : P'.Modules)
    (j : P' ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData F).relProj)
    (hj : j ≫ (SymmetricAlgebraSheaf.gradedAlgebraData F).relProjHom = q ≫ U.ι)
    (w : (Scheme.Modules.tensorPullback j).obj D.line ≅ L')
    (qu : (Scheme.Modules.tensorPullback q).obj
      ((Scheme.Modules.tensorPullback U.ι).obj F) ⟶ L')
    (hopen : (projectiveBundlePullbackComp j
        (SymmetricAlgebraSheaf.gradedAlgebraData F).relProjHom).inv.app F ≫
        (Scheme.Modules.tensorPullback j).map D.quotient ≫ w.hom =
      (projectiveBundlePullbackCongr hj).hom.app F ≫
        (projectiveBundlePullbackComp q U.ι).inv.app F ≫ qu) :
    quotientDiagramCondition qu (⟨(realizationOfQuotient F D c).A.data.relProj, j,
      (realizationOfQuotient F D c).A.data.relProjHom,
      (realizationOfQuotient F D c).L, (realizationOfQuotient F D c).quotient, hj, w⟩ :
      QuotientDiagram q U.ι F L') := by
  exact (congrArg (quotientDiagramCondition qu)
    (realizationDiagram_eq F D c U q L' j hj w)).mp hopen

-- Inlining the supplied instance avoids expensive dependent-type comparisons.

private theorem frameChartOfQuotient {B : Scheme.{u}} (F : B.Modules)
    [F.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient F)
    (c : ∀ (U V : B.affineOpens) (h : U ≤ V),
      SymmetricProjTautologicalCharts.NormalizedAffineRestriction F D U V h)
    (n : ℕ) (U : B.Opens) (e : B.ModuleFrame F U (n + 1)) :
    Nonempty (ProjectiveBundleFrameChart (realizationOfQuotient F D c) n U e) := by
  classical
  obtain ⟨hE, DU, j, hj, w, hw⟩ :=
    SymmetricProjTautologicalCharts.open_compatibility_of_normalized_quotient B F D U
  -- Keep the same witness used in the restricted graded algebra.
  letI := hE
  obtain ⟨a, ha, hr⟩ := exists_restricted_pullback_iso
    (SymmetricAlgebraSheaf.gradedAlgebraData F).relProjHom U
    (SymmetricAlgebraSheaf.gradedAlgebraData
      ((Scheme.Modules.tensorPullback U.ι).obj F)).relProjHom j hj
  obtain ⟨eRel, eStd, tU, hRel, hStd, hcoord⟩ :=
    normalized_free_comparison ((Scheme.Modules.tensorPullback U.ι).obj F) DU n e
  have ho := normalize_quotient_square j
    (SymmetricAlgebraSheaf.gradedAlgebraData
      ((Scheme.Modules.tensorPullback U.ι).obj F)).relProjHom
    (SymmetricAlgebraSheaf.gradedAlgebraData F).relProjHom U.ι hj.w F D.line DU.line
    D.quotient DU.quotient w hw
  have hoR := realization_quotient_square F D c U (SymmetricAlgebraSheaf.gradedAlgebraData
      ((Scheme.Modules.tensorPullback U.ι).obj F)).relProjHom DU.line
    j hj.w w DU.quotient ho
  exact frameChartOfGivenComparison (realizationOfQuotient F D c) n U e
    (SymmetricAlgebraSheaf.gradedAlgebraData
      ((Scheme.Modules.tensorPullback U.ι).obj F)).relProjHom DU.line
    DU.quotient j hj.w a ha hr w hoR eRel eStd tU hRel hStd hcoord

/-- Existence of the frame models, without the properness or coherence conclusions.
Source: Stacks Project, Constructions, Tags 01OB, 01OE, 01NR, 01MN and 01MS;
steps 1--4 of lem-pur-projective-bundle-tautological-geometry.
(blueprint: lem-pur-projective-bundle-frame-models).

Proof: on every affine base open take the symmetric algebra of module sections.
Use the symmetric-degree grading and the coefficientwise restriction maps; the
symmetric-algebra base-change isomorphism gives quasi-coherence in every degree.
Relative Proj glues these affine Proj schemes. On each standard open D_+(f), glue
the degree-one localized modules by a/f^m mapping to the same homogeneous fraction
on refinements. The identity and triple-overlap equations follow by composing the
coefficient maps. The module-sheaf gluing theorem gives L and its affine twist charts.
The local maps sending v to iota(v)/1 agree with restriction and give the quotient
by pullback adjunction. Their generator equations hold by their definition.
For any frame on an open U, the symmetric universal property identifies its
algebra with the polynomial algebra, preserving every degree. Relative Proj
functoriality gives the relative and polynomial charts over U. The degree-one
fraction maps identify their twists and carry T_i to the frame quotient. On
D_+(T_i), multiplication by T_i identifies degree zero with degree one, and the
inverse divides by T_i. Thus the specified section is a free generator. On an
overlap T_i=(T_i/T_j)T_j, giving exactly the transition field. The constructions
agree on affine refinements of nonaffine overlaps, so apply to every frame on U.
Make these choices simultaneously for all B,F of the stipulated rank. The empty
base has empty charts and the same gluing argument applies. -/
theorem exists_projectiveBundleFrameModels (n : ℕ) :
    Nonempty (ProjectiveBundleFrameModels.{u} n) := by
  classical
  have h : ∀ (B : Scheme.{u}) (F : B.Modules) (_ : projectiveBundleRank B n F),
      ∃ D : ProjectiveBundleRealization B F,
        ∀ (U : B.Opens) (e : B.ModuleFrame F U (n + 1)),
          Nonempty (ProjectiveBundleFrameChart D n U e) := by
    intro B F hF
    have : F.IsFiniteLocallyFreeOfRank (n + 1) := hF
    have : F.IsLocallyFree :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree F (n + 1)
    have : F.IsQuasicoherent := inferInstance
    obtain ⟨D, hD⟩ :=
      SymmetricProjTautologicalCharts.exists_normalized_quotient_with_affine_restriction B F
    let c := fun U V h ↦ Classical.choice (hD U V h)
    refine ⟨realizationOfQuotient F D c, ?_⟩
    intro U e
    exact frameChartOfQuotient F D c n U e
  choose bundles frames using h
  exact ⟨{ bundle := bundles
           frame := fun B F hF U e ↦ Classical.choice (frames B F hF U e) }⟩

end AlgebraicGeometry
