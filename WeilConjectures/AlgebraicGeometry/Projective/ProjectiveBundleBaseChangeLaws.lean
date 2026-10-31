/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleBaseChangeFamily
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundlePullbackUnitLaws
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coherence laws for normalized projective-bundle base-change data
Source: Stacks Project, Constructions, Tag 01O3.
(blueprint: lem-pur-projective-bundle-base-change-laws). -/

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

section

-- Adjunction units determine the pullback of sections and its naturality.
private theorem section_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F G : Y.Modules} (a : F ⟶ G) {U : Y.Opens} (m : Γ(F, U)) :
    ((Scheme.Modules.tensorPullback g).map a).app (g ⁻¹ᵁ U)
      (projectiveBundlePullbackSection g m) =
      projectiveBundlePullbackSection g (a.app U m) := by
  unfold projectiveBundlePullbackSection
  have he := congrArg (fun t ↦ t.app U m)
    ((projectiveBundlePullbackAdjunction g).unit.naturality a).symm
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Functor.comp_map, Functor.id_map, ConcreteCategory.comp_apply] at he
  erw [he]
  rfl

private theorem tensor_iso_section {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F : Y.Modules} {U : Y.Opens} (m : Γ(F, U)) :
    ((projectiveBundleTensorPullbackIso g).hom.app F).app (g ⁻¹ᵁ U)
      (projectiveBundlePullbackSection g m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).app U m := by
  unfold projectiveBundleTensorPullbackIso projectiveBundlePullbackSection
    projectiveBundlePullbackAdjunction
  have he := congrArg (fun t ↦ t.app U m)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g))
      (Scheme.Modules.pullbackPushforwardAdjunction g) F)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    ConcreteCategory.comp_apply] at he
  erw [he]
  rfl

private theorem section_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {F : Z.Modules} {U : Z.Opens} (m : Γ(F, U)) :
    ((projectiveBundlePullbackComp f g).hom.app F).app ((f ≫ g) ⁻¹ᵁ U)
      (projectiveBundlePullbackSection f (projectiveBundlePullbackSection g m)) =
      projectiveBundlePullbackSection (f ≫ g) m := by
  have hu := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv F
  erw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hu
  have hue := congrArg (fun t ↦ t.app U m) hu
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    ConcreteCategory.comp_apply] at hue
  change ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
    ((Scheme.Modules.pullback g).obj F)).app (g ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).app U m) =
    ((Scheme.Modules.pullbackComp f g).inv.app F).app ((f ≫ g) ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app F).app U m) at hue
  apply_fun (fun t ↦ ((projectiveBundleTensorPullbackIso (f ≫ g)).hom.app F).app
    ((f ≫ g) ⁻¹ᵁ U) t) using (ConcreteCategory.bijective_of_isIso _).injective
  dsimp only
  erw [tensor_iso_section]
  unfold projectiveBundlePullbackComp
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Iso.symm_hom]
  erw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_app]
  simp only [Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
  simp only [Scheme.Hom.comp_preimage, Functor.comp_obj]
  erw [section_naturality f ((projectiveBundleTensorPullbackIso g).hom.app F)
    (projectiveBundlePullbackSection g m), tensor_iso_section g m,
    tensor_iso_section f _, hue]
  erw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_app]
  rfl

private theorem section_restrict {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F : Y.Modules} {U V : Y.Opens} (h : V ≤ U) (m : Γ(F, U)) :
    ((Scheme.Modules.tensorPullback g).obj F).presheaf.map
      (homOfLE (g.preimage_mono h)).op (projectiveBundlePullbackSection g m) =
      projectiveBundlePullbackSection g (F.presheaf.map (homOfLE h).op m) := by
  unfold projectiveBundlePullbackSection
  have he := (Scheme.Modules.Hom.app_presheaf_map
    ((projectiveBundlePullbackAdjunction g).unit.app F) (homOfLE h) m).symm
  simp only [Functor.comp_obj, Functor.id_obj,
    Scheme.Modules.pushforward_obj_presheaf_map] at he
  erw [he]
  rfl

private theorem hom_restrict {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) {U V : X.Opens} (h : V ≤ U) (m : Γ(F, U)) :
    G.presheaf.map (homOfLE h).op (a.app U m) =
      a.app V (F.presheaf.map (homOfLE h).op m) := by
  exact (Scheme.Modules.Hom.app_presheaf_map a (homOfLE h) m).symm

private theorem section_comp_restrict {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {F : Z.Modules}
    {U : Z.Opens} {V : Y.Opens} {W : X.Opens}
    (hv : V ≤ g ⁻¹ᵁ U) (hw : W ≤ f ⁻¹ᵁ V) (m : Γ(F, U)) :
    ((projectiveBundlePullbackComp f g).hom.app F).app W
      (((Scheme.Modules.tensorPullback f).obj
        ((Scheme.Modules.tensorPullback g).obj F)).presheaf.map (homOfLE hw).op
        (projectiveBundlePullbackSection f
          (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE hv).op
            (projectiveBundlePullbackSection g m)))) =
    ((Scheme.Modules.tensorPullback (f ≫ g)).obj F).presheaf.map
      (homOfLE (hw.trans (f.preimage_mono hv))).op
        (projectiveBundlePullbackSection (f ≫ g) m) := by
  erw [← section_restrict, ← CategoryTheory.Functor.map_comp_apply]
  change ((projectiveBundlePullbackComp f g).hom.app F).app W
    (((Scheme.Modules.tensorPullback f).obj
      ((Scheme.Modules.tensorPullback g).obj F)).presheaf.map
      (homOfLE (hw.trans (f.preimage_mono hv))).op
        (projectiveBundlePullbackSection f (projectiveBundlePullbackSection g m))) = _
  erw [← hom_restrict ((projectiveBundlePullbackComp f g).hom.app F)
    (hw.trans (f.preimage_mono hv))
    (projectiveBundlePullbackSection f (projectiveBundlePullbackSection g m)),
    section_comp f g m]

private theorem section_comp_restrict_inv {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {F : Z.Modules}
    {U : Z.Opens} {V : Y.Opens} {W : X.Opens}
    (hv : V ≤ g ⁻¹ᵁ U) (hw : W ≤ f ⁻¹ᵁ V) (m : Γ(F, U)) :
    ((projectiveBundlePullbackComp f g).inv.app F).app W
      (((Scheme.Modules.tensorPullback (f ≫ g)).obj F).presheaf.map
        (homOfLE (hw.trans (f.preimage_mono hv))).op
        (projectiveBundlePullbackSection (f ≫ g) m)) =
    ((Scheme.Modules.tensorPullback f).obj
      ((Scheme.Modules.tensorPullback g).obj F)).presheaf.map (homOfLE hw).op
      (projectiveBundlePullbackSection f
        (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE hv).op
          (projectiveBundlePullbackSection g m))) := by
  erw [← section_comp_restrict f g hv hw m, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app]
  rfl

private theorem coefficient_comp
    {B₀ B₁ B₂ : Scheme.{u}} {F₀ : B₀.Modules} {F₁ : B₁.Modules} {F₂ : B₂.Modules}
    {D₀ : ProjectiveBundleRealization B₀ F₀} {D₁ : ProjectiveBundleRealization B₁ F₁}
    {D₂ : ProjectiveBundleRealization B₂ F₂}
    {g : B₁ ⟶ B₀} {h : B₂ ⟶ B₁}
    {e : F₁ ≅ (Scheme.Modules.tensorPullback g).obj F₀}
    {e' : F₂ ≅ (Scheme.Modules.tensorPullback h).obj F₁}
    (a : ProjectiveBundleBaseChangeDatum D₀ D₁ g e)
    (b : ProjectiveBundleBaseChangeDatum D₁ D₂ h e')
    (c : ProjectiveBundleBaseChangeDatum D₀ D₂ (h ≫ g)
      (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
        (projectiveBundlePullbackComp h g).app F₀))
    {U₀ : B₀.affineOpens} {U₁ : B₁.affineOpens} {U₂ : B₂.affineOpens}
    (h₁ : U₁.1 ≤ g ⁻¹ᵁ U₀.1) (h₂ : U₂.1 ≤ h ⁻¹ᵁ U₁.1) :
    c.comparison.map (h₂.trans (h.preimage_mono h₁)) =
      (b.comparison.map h₂).comp (a.comparison.map h₁) := by
  apply GradedRingHom.ext
  intro z
  obtain ⟨z, rfl⟩ := (D₀.A.sectionEquiv U₀).surjective z
  induction z using SymmetricAlgebra.induction with
  | algebraMap r =>
    simp only [AlgEquiv.commutes, GradedRingHom.comp_apply,
      (a.comparison.isGradedBaseChangeAlong h₁).map_algebraMap,
      (b.comparison.isGradedBaseChangeAlong h₂).map_algebraMap,
      (c.comparison.isGradedBaseChangeAlong
        (h₂.trans (h.preimage_mono h₁))).map_algebraMap]
    exact congrArg (algebraMap Γ(B₂, U₂.1) _) (congrArg
      (fun k : Γ(B₀, U₀.1) ⟶ Γ(B₂, U₂.1) ↦ k r)
      (Scheme.Hom.appLE_comp_appLE h g U₀.1 U₁.1 U₂.1 h₁ h₂)).symm
  | ι m =>
    erw [GradedRingHom.comp_apply, a.generator, b.generator, c.generator]
    apply congrArg (fun t ↦ D₂.A.sectionEquiv U₂ (SymmetricAlgebra.ι _ _ t))
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    erw [section_comp_restrict_inv h g h₁ h₂ m]
    erw [← hom_restrict ((Scheme.Modules.tensorPullback h).map e.inv) h₂ _,
      section_naturality h e.inv _]
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem map_comp
    {B₀ B₁ B₂ : Scheme.{u}} {F₀ : B₀.Modules} {F₁ : B₁.Modules} {F₂ : B₂.Modules}
    {D₀ : ProjectiveBundleRealization B₀ F₀} {D₁ : ProjectiveBundleRealization B₁ F₁}
    {D₂ : ProjectiveBundleRealization B₂ F₂}
    {g : B₁ ⟶ B₀} {h : B₂ ⟶ B₁}
    {e : F₁ ≅ (Scheme.Modules.tensorPullback g).obj F₀}
    {e' : F₂ ≅ (Scheme.Modules.tensorPullback h).obj F₁}
    (a : ProjectiveBundleBaseChangeDatum D₀ D₁ g e)
    (b : ProjectiveBundleBaseChangeDatum D₁ D₂ h e')
    (c : ProjectiveBundleBaseChangeDatum D₀ D₂ (h ≫ g)
      (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
        (projectiveBundlePullbackComp h g).app F₀))
    : c.map = b.map ≫ a.map := by
  let T := {q : B₂.affineOpens × B₁.affineOpens × B₀.affineOpens //
    q.1.1 ≤ h ⁻¹ᵁ q.2.1.1 ∧ q.2.1.1 ≤ g ⁻¹ᵁ q.2.2.1}
  have hcovers (x : D₂.A.data.relProj) :
      ∃ q : T, ∃ y, D₂.A.data.relProjι q.1.1 y = x := by
    let z := D₂.A.data.relProjHom x
    obtain ⟨U₀, hU₀⟩  := Scheme.GradedAlgebraData.exists_affineOpens_mem (g (h z))
    obtain ⟨V, hV, hzV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      B₁.isBasis_affineOpens (show h z ∈ g ⁻¹ᵁ U₀.1 from hU₀)
    let U₁ : B₁.affineOpens := ⟨V, hV⟩
    obtain ⟨W, hW, hzW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      B₂.isBasis_affineOpens (show z ∈ h ⁻¹ᵁ U₁.1 from hzV)
    let U₂ : B₂.affineOpens := ⟨W, hW⟩
    refine ⟨⟨(U₂, U₁, U₀), hWle, hVle⟩, ?_⟩
    have hx : x ∈ D₂.A.data.relProjHom ⁻¹ᵁ U₂.1 := hzW
    rw [D₂.A.data.relProjHom_preimage U₂] at hx
    exact hx
  let C : D₂.A.data.relProj.OpenCover := Scheme.Cover.mkOfCovers T
    (fun q ↦ Proj (D₂.A.data.grading q.1.1))
    (fun q ↦ D₂.A.data.relProjι q.1.1) hcovers
  apply C.hom_ext
  intro q
  change T at q
  change D₂.A.data.relProjι q.1.1 ≫ c.map =
    D₂.A.data.relProjι q.1.1 ≫ b.map ≫ a.map
  rw [c.map_eq, b.map_eq, a.map_eq, ← Category.assoc,
    b.comparison.relProjι_relProjComparison q.2.1,
    c.comparison.relProjι_relProjComparison (q.2.1.trans (h.preimage_mono q.2.2))]
  simp only [Scheme.GradedAlgebraData.PullbackData.localComparison, Category.assoc]
  rw [a.comparison.relProjι_relProjComparison q.2.2]
  simp only [Scheme.GradedAlgebraData.PullbackData.localComparison, ← Category.assoc]
  rw [← Proj.map_comp]
  exact congrArg (· ≫ D₀.A.data.relProjι q.1.2.2)
    (Proj.map_congr (coefficient_comp a b c q.2.2 q.2.1) _ _)

private theorem congr_eqToHom_inv {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (e : f = g) (F : Y.Modules) :
    (projectiveBundlePullbackCongr e).inv.app F =
      eqToHom (congrArg (fun k ↦ (Scheme.Modules.tensorPullback k).obj F) e.symm) := by
  subst g
  simp [projectiveBundlePullbackCongr]

private theorem congr_app_refl {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    (e : f = f) : (projectiveBundlePullbackCongr e).app F = Iso.refl _ := by
  simp [projectiveBundlePullbackCongr]
  rfl

private theorem comp_assoc_inv {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Z.Modules) :
    (projectiveBundlePullbackComp (f ≫ g) h).inv.app F ≫
      (projectiveBundlePullbackComp f g).inv.app ((Scheme.Modules.tensorPullback h).obj F) =
    (projectiveBundlePullbackCongr (Category.assoc f g h)).hom.app F ≫
      (projectiveBundlePullbackComp f (g ≫ h)).inv.app F ≫
      (Scheme.Modules.tensorPullback f).map ((projectiveBundlePullbackComp g h).inv.app F) := by
  have ha := congrArg (fun t ↦ t.app F) (projectiveBundlePullback_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at ha
  simp only [eqToHom_app] at ha
  rw [← congr_eqToHom_inv (Category.assoc f g h) F] at ha
  apply (cancel_epi ((projectiveBundlePullbackCongr (Category.assoc f g h)).app F).inv).mp
  apply (cancel_mono ((projectiveBundlePullbackComp f g).app
    ((Scheme.Modules.tensorPullback h).obj F)).hom).mp
  apply (cancel_mono ((projectiveBundlePullbackComp (f ≫ g) h).app F).hom).mp
  simp only [Iso.app_hom, Iso.app_inv, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  erw [Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  exact ha.symm

private theorem comp_assoc_first {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Z.Modules) :
    (projectiveBundlePullbackComp f g).inv.app ((Scheme.Modules.tensorPullback h).obj F) ≫
      (Scheme.Modules.tensorPullback f).map ((projectiveBundlePullbackComp g h).hom.app F) =
    (projectiveBundlePullbackComp (f ≫ g) h).hom.app F ≫
      (projectiveBundlePullbackCongr (Category.assoc f g h)).hom.app F ≫
      (projectiveBundlePullbackComp f (g ≫ h)).inv.app F := by
  apply (cancel_epi ((projectiveBundlePullbackComp (f ≫ g) h).app F).inv).mp
  simp only [Iso.app_inv]
  rw [← Category.assoc, comp_assoc_inv f g h F]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem comp_assoc_middle {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Z.Modules) :
    (projectiveBundlePullbackComp f (g ≫ h)).inv.app F ≫
      (Scheme.Modules.tensorPullback f).map ((projectiveBundlePullbackComp g h).inv.app F) ≫
      (projectiveBundlePullbackComp f g).hom.app ((Scheme.Modules.tensorPullback h).obj F) =
    (projectiveBundlePullbackCongr (Category.assoc f g h)).inv.app F ≫
      (projectiveBundlePullbackComp (f ≫ g) h).inv.app F := by
  have ha := congrArg (fun t ↦ t.app F) (projectiveBundlePullback_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at ha
  simp only [eqToHom_app] at ha
  rw [← congr_eqToHom_inv (Category.assoc f g h) F] at ha
  apply (cancel_mono ((projectiveBundlePullbackComp (f ≫ g) h).app F).hom).mp
  simpa only [Iso.app_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using ha

private theorem object_transport_chain {α C : Type*} [Category C]
    (P : α → C) {f₀ f₁ f₂ f₃ f₄ f₅ : α}
    (e₁ : f₀ = f₁) (e₂ : f₁ = f₂) (e₃ : f₃ = f₂) (e₄ : f₃ = f₄)
    (e₅ : f₄ = f₅) (e : f₀ = f₅) :
    eqToHom (congrArg P e₁) ≫ eqToHom (congrArg P e₂) ≫
      eqToHom (congrArg P e₃.symm) ≫ eqToHom (congrArg P e₄) ≫
      eqToHom (congrArg P e₅) = eqToHom (congrArg P e) := by
  subst f₁
  subst f₂
  subst f₃
  subst f₄
  subst f₅
  simp

private theorem congr_nat_chain {X Y : Scheme.{u}} {f₀ f₁ f₂ f₃ f₄ f₅ : X ⟶ Y}
    (e₁ : f₀ = f₁) (e₂ : f₁ = f₂) (e₃ : f₃ = f₂) (e₄ : f₃ = f₄)
    (e₅ : f₄ = f₅) (e : f₀ = f₅) :
    (projectiveBundlePullbackCongr e₁).hom ≫
      (projectiveBundlePullbackCongr e₂).hom ≫
      (projectiveBundlePullbackCongr e₃).inv ≫
      (projectiveBundlePullbackCongr e₄).hom ≫
      (projectiveBundlePullbackCongr e₅).hom =
      (projectiveBundlePullbackCongr e).hom := by
  unfold projectiveBundlePullbackCongr
  exact object_transport_chain Scheme.Modules.tensorPullback e₁ e₂ e₃ e₄ e₅ e

private theorem congr_hom_chain {X Y : Scheme.{u}} {f₀ f₁ f₂ f₃ f₄ f₅ : X ⟶ Y}
    (e₁ : f₀ = f₁) (e₂ : f₁ = f₂) (e₃ : f₃ = f₂) (e₄ : f₃ = f₄)
    (e₅ : f₄ = f₅) (e : f₀ = f₅) (F : Y.Modules) :
    (projectiveBundlePullbackCongr e₁).hom.app F ≫
      (projectiveBundlePullbackCongr e₂).hom.app F ≫
      (projectiveBundlePullbackCongr e₃).inv.app F ≫
      (projectiveBundlePullbackCongr e₄).hom.app F ≫
      (projectiveBundlePullbackCongr e₅).hom.app F =
      (projectiveBundlePullbackCongr e).hom.app F := by
  have h := congrArg (fun t ↦ t.app F) (congr_nat_chain e₁ e₂ e₃ e₄ e₅ e)
  simpa only [NatTrans.comp_app] using h
private theorem map_three {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B C' D' : C} (a : A ⟶ B) (b : B ⟶ C') (c : C' ⟶ D') :
    F.map (a ≫ b ≫ c) = F.map a ≫ F.map b ≫ F.map c := by
  simp only [Functor.map_comp]

-- Prove the path-replacement algebra before specializing it to module pullbacks.
private theorem categorical_paste {C : Type*} [Category C]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ O₁₁ O₁₂ O₁₃ O₁₄ : C}
    {a : O₀ ⟶ O₁} {b : O₁ ⟶ O₂} {c : O₂ ⟶ O₃} {d : O₃ ⟶ O₄}
    {e : O₄ ⟶ O₅} {f : O₅ ⟶ O₆} {g : O₆ ⟶ O₇} {m : O₁ ⟶ O₄}
    {h : O₀ ⟶ O₈} {q : O₈ ⟶ O₉} {a' : O₉ ⟶ O₂}
    {r : O₉ ⟶ O₁₀} {b' : O₁₀ ⟶ O₃} {s : O₁₀ ⟶ O₁₁} {c' : O₁₁ ⟶ O₅}
    {t : O₁₁ ⟶ O₁₂} {d' : O₁₂ ⟶ O₆} {u : O₁₂ ⟶ O₁₃}
    {e' : O₁₃ ⟶ O₁₄} {f' : O₁₄ ⟶ O₇} {k : O₈ ⟶ O₁₃}
    (h₀ : m = b ≫ c ≫ d) (h₁ : a ≫ b = h ≫ q ≫ a') (h₂ : a' ≫ c = r ≫ b')
    (h₃ : b' ≫ d ≫ e = s ≫ c') (h₄ : c' ≫ f = t ≫ d')
    (h₅ : d' ≫ g = u ≫ e' ≫ f') (h₆ : q ≫ r ≫ s ≫ t ≫ u = k) :
    a ≫ m ≫ e ≫ f ≫ g = h ≫ k ≫ e' ≫ f' := by
  rw [h₀, Category.assoc, Category.assoc, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃,
    reassoc_of% h₄, h₅, reassoc_of% h₆]

-- Give comparison components explicit source objects to avoid costly conversions.
private noncomputable def compApp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Modules) :
    (Scheme.Modules.tensorPullback f).obj ((Scheme.Modules.tensorPullback g).obj F) ≅
      (Scheme.Modules.tensorPullback (f ≫ g)).obj F :=
  (projectiveBundlePullbackComp f g).app F

private theorem comp_assoc_inv_app {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Z.Modules) :
    (compApp (f ≫ g) h F).inv ≫
      (compApp f g ((Scheme.Modules.tensorPullback h).obj F)).inv =
    (projectiveBundlePullbackCongr (Category.assoc f g h)).hom.app F ≫
      (compApp f (g ≫ h) F).inv ≫
      (Scheme.Modules.tensorPullback f).map ((compApp g h F).inv) := by
  simpa only [compApp, Iso.app_hom, Iso.app_inv] using comp_assoc_inv f g h F

private theorem comp_assoc_first_app {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Z.Modules) :
    (compApp f g ((Scheme.Modules.tensorPullback h).obj F)).inv ≫
      (Scheme.Modules.tensorPullback f).map ((compApp g h F).hom) =
    (compApp (f ≫ g) h F).hom ≫
      (projectiveBundlePullbackCongr (Category.assoc f g h)).hom.app F ≫
      (compApp f (g ≫ h) F).inv := by
  simpa only [compApp, Iso.app_hom, Iso.app_inv] using comp_assoc_first f g h F

private theorem comp_assoc_middle_app {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Z.Modules) :
    (compApp f (g ≫ h) F).inv ≫
      (Scheme.Modules.tensorPullback f).map ((compApp g h F).inv) ≫
      (compApp f g ((Scheme.Modules.tensorPullback h).obj F)).hom =
    (projectiveBundlePullbackCongr (Category.assoc f g h)).inv.app F ≫
      (compApp (f ≫ g) h F).inv := by
  simpa only [compApp, Iso.app_hom, Iso.app_inv] using comp_assoc_middle f g h F

private theorem comp_congr_right_app {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    {g g' : Y ⟶ Z} (e : g = g') (F : Z.Modules) :
    (compApp f g F).inv ≫
      (Scheme.Modules.tensorPullback f).map ((projectiveBundlePullbackCongr e).hom.app F) =
    (projectiveBundlePullbackCongr (congrArg (f ≫ ·) e)).hom.app F ≫
      (compApp f g' F).inv := by
  subst g'
  simp [projectiveBundlePullbackCongr]

private theorem comp_congr_left_app {X Y Z : Scheme.{u}} {f f' : X ⟶ Y}
    (e : f = f') (g : Y ⟶ Z) (F : Z.Modules) :
    (compApp f g F).inv ≫
      (projectiveBundlePullbackCongr e).hom.app ((Scheme.Modules.tensorPullback g).obj F) =
    (projectiveBundlePullbackCongr (congrArg (· ≫ g) e)).hom.app F ≫
      (compApp f' g F).inv := by
  subst f'
  simp [projectiveBundlePullbackCongr]

private theorem square_paste {P₀ P₁ P₂ B₀ B₁ B₂ : Scheme.{u}}
    (r : P₁ ⟶ P₀) (s : P₂ ⟶ P₁) (p₀ : P₀ ⟶ B₀)
    (p₁ : P₁ ⟶ B₁) (p₂ : P₂ ⟶ B₂) (g : B₁ ⟶ B₀) (h : B₂ ⟶ B₁)
    (hr : r ≫ p₀ = p₁ ≫ g) (hs : s ≫ p₁ = p₂ ≫ h)
    (hc : (s ≫ r) ≫ p₀ = p₂ ≫ (h ≫ g)) (F : B₀.Modules) :
    (compApp s r ((Scheme.Modules.tensorPullback p₀).obj F)).inv ≫
      (Scheme.Modules.tensorPullback s).map
        ((compApp r p₀ F).hom ≫
          (projectiveBundlePullbackCongr hr).hom.app F ≫
          (compApp p₁ g F).inv) ≫
      (compApp s p₁ ((Scheme.Modules.tensorPullback g).obj F)).hom ≫
      (projectiveBundlePullbackCongr hs).hom.app ((Scheme.Modules.tensorPullback g).obj F) ≫
      (compApp p₂ h ((Scheme.Modules.tensorPullback g).obj F)).inv =
    (compApp (s ≫ r) p₀ F).hom ≫
      (projectiveBundlePullbackCongr hc).hom.app F ≫
      (compApp p₂ (h ≫ g) F).inv ≫
      (Scheme.Modules.tensorPullback p₂).map ((compApp h g F).inv) := by
  exact categorical_paste (C := P₂.Modules)
    (O₀ := (Scheme.Modules.tensorPullback (s ≫ r)).obj
      ((Scheme.Modules.tensorPullback p₀).obj F))
    (O₁ := (Scheme.Modules.tensorPullback s).obj
      ((Scheme.Modules.tensorPullback r).obj ((Scheme.Modules.tensorPullback p₀).obj F)))
    (O₂ := (Scheme.Modules.tensorPullback s).obj
      ((Scheme.Modules.tensorPullback (r ≫ p₀)).obj F))
    (O₃ := (Scheme.Modules.tensorPullback s).obj
      ((Scheme.Modules.tensorPullback (p₁ ≫ g)).obj F))
    (O₄ := (Scheme.Modules.tensorPullback s).obj
      ((Scheme.Modules.tensorPullback p₁).obj ((Scheme.Modules.tensorPullback g).obj F)))
    (O₅ := (Scheme.Modules.tensorPullback (s ≫ p₁)).obj
      ((Scheme.Modules.tensorPullback g).obj F))
    (O₆ := (Scheme.Modules.tensorPullback (p₂ ≫ h)).obj
      ((Scheme.Modules.tensorPullback g).obj F))
    (O₇ := (Scheme.Modules.tensorPullback p₂).obj
      ((Scheme.Modules.tensorPullback h).obj ((Scheme.Modules.tensorPullback g).obj F)))
    (O₈ := (Scheme.Modules.tensorPullback ((s ≫ r) ≫ p₀)).obj F)
    (O₉ := (Scheme.Modules.tensorPullback (s ≫ (r ≫ p₀))).obj F)
    (O₁₀ := (Scheme.Modules.tensorPullback (s ≫ (p₁ ≫ g))).obj F)
    (O₁₁ := (Scheme.Modules.tensorPullback ((s ≫ p₁) ≫ g)).obj F)
    (O₁₂ := (Scheme.Modules.tensorPullback ((p₂ ≫ h) ≫ g)).obj F)
    (O₁₃ := (Scheme.Modules.tensorPullback (p₂ ≫ (h ≫ g))).obj F)
    (O₁₄ := (Scheme.Modules.tensorPullback p₂).obj
      ((Scheme.Modules.tensorPullback (h ≫ g)).obj F))
    (map_three (C := P₁.Modules) (D := P₂.Modules) (Scheme.Modules.tensorPullback s) _ _ _)
    (comp_assoc_first_app s r p₀ F) (comp_congr_right_app s hr F)
    (comp_assoc_middle_app s p₁ g F) (comp_congr_left_app hs g F)
    (comp_assoc_inv_app p₂ h g F) (congr_hom_chain (Category.assoc s r p₀) (congrArg (s ≫ ·) hr)
      (Category.assoc s p₁ g) (congrArg (· ≫ g) hs) (Category.assoc p₂ h g) hc F)

@[reassoc]
private theorem compApp_inv_naturality {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {F G : Z.Modules} (q : F ⟶ G) :
    (Scheme.Modules.tensorPullback (f ≫ g)).map q ≫ (compApp f g G).inv =
      (compApp f g F).inv ≫
        (Scheme.Modules.tensorPullback f).map ((Scheme.Modules.tensorPullback g).map q) := by
  simpa only [compApp, Iso.app_inv, Functor.comp_map] using
    (projectiveBundlePullbackComp f g).inv.naturality q

@[reassoc]
private theorem compApp_hom_naturality {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {F G : Z.Modules} (q : F ⟶ G) :
    (Scheme.Modules.tensorPullback f).map ((Scheme.Modules.tensorPullback g).map q) ≫
      (compApp f g G).hom =
    (compApp f g F).hom ≫ (Scheme.Modules.tensorPullback (f ≫ g)).map q := by
  simpa only [compApp, Iso.app_hom, Functor.comp_map] using
    (projectiveBundlePullbackComp f g).hom.naturality q

private theorem theta_comp
    {B₀ B₁ B₂ : Scheme.{u}} {F₀ : B₀.Modules} {F₁ : B₁.Modules} {F₂ : B₂.Modules}
    {D₀ : ProjectiveBundleRealization B₀ F₀} {D₁ : ProjectiveBundleRealization B₁ F₁}
    {D₂ : ProjectiveBundleRealization B₂ F₂}
    {g : B₁ ⟶ B₀} {h : B₂ ⟶ B₁}
    {e : F₁ ≅ (Scheme.Modules.tensorPullback g).obj F₀}
    {e' : F₂ ≅ (Scheme.Modules.tensorPullback h).obj F₁}
    (a : ProjectiveBundleBaseChangeDatum D₀ D₁ g e)
    (b : ProjectiveBundleBaseChangeDatum D₁ D₂ h e')
    (ho : (b.map ≫ a.map) ≫ D₀.A.data.relProjHom = D₂.A.data.relProjHom ≫ (h ≫ g)) :
    projectiveBundleThetaQuotientLaw D₀ D₂ (h ≫ g)
      (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
        (projectiveBundlePullbackComp h g).app F₀) (b.map ≫ a.map) ho
      (((projectiveBundlePullbackComp b.map a.map).app D₀.L).symm ≪≫
        (Scheme.Modules.tensorPullback b.map).mapIso a.theta ≪≫ b.theta) := by
  have ha : (Scheme.Modules.tensorPullback a.map).map D₀.quotient ≫ a.theta.hom =
      (compApp a.map D₀.A.data.relProjHom F₀).hom ≫
      (projectiveBundlePullbackCongr a.over).hom.app F₀ ≫
      (compApp D₁.A.data.relProjHom g F₀).inv ≫
      (Scheme.Modules.tensorPullback D₁.A.data.relProjHom).map e.inv ≫ D₁.quotient := by
    exact a.theta_quotient
  have hb : (Scheme.Modules.tensorPullback b.map).map D₁.quotient ≫ b.theta.hom =
      (compApp b.map D₁.A.data.relProjHom F₁).hom ≫
      (projectiveBundlePullbackCongr b.over).hom.app F₁ ≫
      (compApp D₂.A.data.relProjHom h F₁).inv ≫
      (Scheme.Modules.tensorPullback D₂.A.data.relProjHom).map e'.inv ≫ D₂.quotient := by
    exact b.theta_quotient
  simp only [projectiveBundleThetaQuotientLaw, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
  change (Scheme.Modules.tensorPullback (b.map ≫ a.map)).map D₀.quotient ≫
      (compApp b.map a.map D₀.L).inv ≫
      (Scheme.Modules.tensorPullback b.map).map a.theta.hom ≫ b.theta.hom =
    (compApp (b.map ≫ a.map) D₀.A.data.relProjHom F₀).hom ≫
      (projectiveBundlePullbackCongr ho).hom.app F₀ ≫
      (compApp D₂.A.data.relProjHom (h ≫ g) F₀).inv ≫
      (Scheme.Modules.tensorPullback D₂.A.data.relProjHom).map
        ((compApp h g F₀).inv ≫ (Scheme.Modules.tensorPullback h).map e.inv ≫ e'.inv) ≫
      D₂.quotient
  rw [compApp_inv_naturality_assoc b.map a.map D₀.quotient]
  rw [← Functor.map_comp_assoc, ha]
  simp only [Functor.map_comp, Category.assoc]
  rw [hb]
  rw [compApp_hom_naturality_assoc b.map D₁.A.data.relProjHom e.inv]
  erw [(projectiveBundlePullbackCongr b.over).hom.naturality_assoc e.inv]
  rw [compApp_inv_naturality_assoc D₂.A.data.relProjHom h e.inv]
  have hp := square_paste a.map b.map D₀.A.data.relProjHom D₁.A.data.relProjHom
    D₂.A.data.relProjHom g h a.over b.over ho F₀
  simp only [Functor.map_comp, Category.assoc] at hp
  rw [reassoc_of% hp]


private theorem theta_transport
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    {r r' : D'.A.data.relProj ⟶ D.A.data.relProj} (hr : r = r')
    (ho : r ≫ D.A.data.relProjHom = D'.A.data.relProjHom ≫ g)
    (ho' : r' ≫ D.A.data.relProjHom = D'.A.data.relProjHom ≫ g)
    (θ : (Scheme.Modules.tensorPullback r').obj D.L ≅ D'.L)
    (hθ : projectiveBundleThetaQuotientLaw D D' g e r' ho' θ) :
    projectiveBundleThetaQuotientLaw D D' g e r ho
      ((projectiveBundlePullbackCongr hr).app D.L ≪≫ θ) := by
  subst r'
  rw [congr_app_refl, Iso.refl_trans]
  exact hθ

end

/-- The map composition law and quotient compatibility of the canonical composite.
Source: Stacks Project, Tag 01O3.
(blueprint: lem-pur-projective-bundle-base-change-laws). -/
structure ProjectiveBundleBaseChangeLaws {n : ℕ}
    {M : ProjectiveBundleFrameModels.{u} n}
    (I : ProjectiveBundleBaseChangeFamily M) where
  baseChange_comp : ∀ {B₀ B₁ B₂ : Scheme.{u}} {F₀ : B₀.Modules} {F₁ : B₁.Modules}
    {F₂ : B₂.Modules} (h₀ : projectiveBundleRank B₀ n F₀)
    (h₁ : projectiveBundleRank B₁ n F₁) (h₂ : projectiveBundleRank B₂ n F₂)
    (g : B₁ ⟶ B₀) (h : B₂ ⟶ B₁)
    (e : F₁ ≅ (Scheme.Modules.tensorPullback g).obj F₀)
    (e' : F₂ ≅ (Scheme.Modules.tensorPullback h).obj F₁),
      (I.baseChange h₀ h₂ (h ≫ g) (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
        (projectiveBundlePullbackComp h g).app F₀)).map =
      (I.baseChange h₁ h₂ h e').map ≫
        (I.baseChange h₀ h₁ g e).map
  baseChange_theta_comp : ∀ {B₀ B₁ B₂ : Scheme.{u}} {F₀ : B₀.Modules} {F₁ : B₁.Modules}
    {F₂ : B₂.Modules} (h₀ : projectiveBundleRank B₀ n F₀)
    (h₁ : projectiveBundleRank B₁ n F₁) (h₂ : projectiveBundleRank B₂ n F₂)
    (g : B₁ ⟶ B₀) (h : B₂ ⟶ B₁)
    (e : F₁ ≅ (Scheme.Modules.tensorPullback g).obj F₀)
    (e' : F₂ ≅ (Scheme.Modules.tensorPullback h).obj F₁),
    let a := I.baseChange h₀ h₂ (h ≫ g) (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
      (projectiveBundlePullbackComp h g).app F₀)
    projectiveBundleThetaQuotientLaw (M.bundle B₀ F₀ h₀) (M.bundle B₂ F₂ h₂)
      (h ≫ g) (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
        (projectiveBundlePullbackComp h g).app F₀) a.map a.over
      ((projectiveBundlePullbackCongr (baseChange_comp h₀ h₁ h₂ g h e e')).app
        (M.bundle B₀ F₀ h₀).L ≪≫
        ((projectiveBundlePullbackComp (I.baseChange h₁ h₂ h e').map
          (I.baseChange h₀ h₁ g e).map).app (M.bundle B₀ F₀ h₀).L).symm ≪≫
        (Scheme.Modules.tensorPullback (I.baseChange h₁ h₂ h e').map).mapIso
          (I.baseChange h₀ h₁ g e).theta ≪≫ (I.baseChange h₁ h₂ h e').theta)

/-- The canonical composite line map preserves the normalized quotient.
Source: Stacks Project, Tag 01O3.
Proof: on chains of affine opens `U₂ ≤ h⁻¹ U₁`, `U₁ ≤ g⁻¹ U₀` the direct and successive
coefficient maps for a composite agree on scalars (`appLE` composition) and send each
generator to the same twice-pulled-back vector: the unit equations for the adjunction
comparisons identify the twice-pulled section with the directly pulled one. Symmetric-algebra
induction gives equality of the graded maps, `Proj.map_comp` equality on the charts, and since
such chains cover the source, open-cover extensionality gives the map law. The composite line
map preserves the quotient by substituting the two quotient equations, then using pullback
naturality and the associative comparisons, pasted along the outside square; transport along
the proved equality of scheme maps gives the asserted quotient-square condition. Equality with
the given theta maps is not asserted. Empty bases cause no exception.
(blueprint: lem-pur-projective-bundle-base-change-laws). -/
theorem exists_projectiveBundleBaseChangeLaws {n : ℕ}
    {M : ProjectiveBundleFrameModels.{u} n} (I : ProjectiveBundleBaseChangeFamily M) :
    Nonempty (ProjectiveBundleBaseChangeLaws I) := by
  refine ⟨{ baseChange_comp := ?_, baseChange_theta_comp := ?_ }⟩
  · intro B₀ B₁ B₂ F₀ F₁ F₂ h₀ h₁ h₂ g h e e'
    exact map_comp (I.baseChange h₀ h₁ g e) (I.baseChange h₁ h₂ h e')
      (I.baseChange h₀ h₂ (h ≫ g)
        (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
          (projectiveBundlePullbackComp h g).app F₀))
  · intro B₀ B₁ B₂ F₀ F₁ F₂ h₀ h₁ h₂ g h e e'
    dsimp only
    let a := I.baseChange h₀ h₁ g e
    let b := I.baseChange h₁ h₂ h e'
    have ho : (b.map ≫ a.map) ≫ (M.bundle B₀ F₀ h₀).A.data.relProjHom =
        (M.bundle B₂ F₂ h₂).A.data.relProjHom ≫ (h ≫ g) := by
      rw [Category.assoc, a.over, ← Category.assoc b.map, b.over, Category.assoc]
    simpa only [Iso.trans_assoc] using theta_transport _ _ _ _
      (map_comp a b (I.baseChange h₀ h₂ (h ≫ g)
        (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
          (projectiveBundlePullbackComp h g).app F₀))) _ ho _ (theta_comp a b ho)

end AlgebraicGeometry
