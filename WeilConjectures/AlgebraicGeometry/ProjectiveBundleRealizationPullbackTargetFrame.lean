/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundlePullbackSectionNormalization
import all WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientPulledChartNormalization
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The target quotient generator on a fixed base-change standard open
(blueprint: lem-pur-projective-bundle-realization-pullback-target-frame).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundleTensorPullbackIso projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction
  Scheme.GradedAlgebraData.relProjHom
  Scheme.GradedAlgebraData.PullbackData.relProjComparison
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι
open Scheme.Modules

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
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

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
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

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
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

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
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

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
private theorem hom_restrict {X : Scheme.{u}} {F G : X.Modules}
    (a : F ⟶ G) {U V : X.Opens} (h : V ≤ U) (m : Γ(F, U)) :
    G.presheaf.map (homOfLE h).op (a.app U m) =
      a.app V (F.presheaf.map (homOfLE h).op m) := by
  exact (Scheme.Modules.Hom.app_presheaf_map a (homOfLE h) m).symm

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
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

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
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

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
private theorem section_congr_restrict {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) {F : Y.Modules} {U : Y.Opens} {V : X.Opens}
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (m : Γ(F, U)) :
    ((projectiveBundlePullbackCongr h).hom.app F).app V
      (((Scheme.Modules.tensorPullback f).obj F).presheaf.map (homOfLE hf).op
        (projectiveBundlePullbackSection f m)) =
      ((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE hg).op
        (projectiveBundlePullbackSection g m) := by
  subst g
  simp [projectiveBundlePullbackCongr]

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
private theorem section_square_restrict {X Y Z T : Scheme.{u}}
    (r : X ⟶ Y) (p : Y ⟶ T) (p' : X ⟶ Z) (g : Z ⟶ T)
    (h : r ≫ p = p' ≫ g) {F : T.Modules} {W : T.Opens} {W' : Z.Opens}
    {O : X.Opens} (hW : W' ≤ g ⁻¹ᵁ W) (hO : O ≤ p' ⁻¹ᵁ W')
    (hS : O ≤ r ⁻¹ᵁ (p ⁻¹ᵁ W)) (x : Γ(F, W)) :
    (((projectiveBundlePullbackComp r p).app F).hom ≫
      (projectiveBundlePullbackCongr h).hom.app F ≫
      ((projectiveBundlePullbackComp p' g).app F).inv).app O
      (((Scheme.Modules.tensorPullback r).obj
        ((Scheme.Modules.tensorPullback p).obj F)).presheaf.map (homOfLE hS).op
          (projectiveBundlePullbackSection r (projectiveBundlePullbackSection p x))) =
      (((Scheme.Modules.tensorPullback p').obj
        ((Scheme.Modules.tensorPullback g).obj F))).presheaf.map (homOfLE hO).op
          (projectiveBundlePullbackSection p'
            (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE hW).op
              (projectiveBundlePullbackSection g x))) := by
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  erw [Scheme.Modules.Hom.app_presheaf_map, section_comp]
  erw [section_congr_restrict h hS (hO.trans (p'.preimage_mono hW)) x]
  exact section_comp_restrict_inv p' g hW hO x

set_option maxHeartbeats 800000 in
-- Keep the coherence evaluation abstract in its schemes and module objects.
private theorem section_square_quotient {X Y Z T : Scheme.{u}}
    (r : X ⟶ Y) (p : Y ⟶ T) (p' : X ⟶ Z) (g : Z ⟶ T)
    (h : r ≫ p = p' ≫ g) {F : T.Modules} {G : Z.Modules} {L : X.Modules}
    (a : (tensorPullback g).obj F ⟶ G) (q : (tensorPullback p').obj G ⟶ L)
    {W : T.Opens} {W' : Z.Opens} {O : X.Opens}
    (hW : W' ≤ g ⁻¹ᵁ W) (hO : O ≤ p' ⁻¹ᵁ W')
    (hS : O ≤ r ⁻¹ᵁ (p ⁻¹ᵁ W)) (x : Γ(F, W)) :
    (((projectiveBundlePullbackComp r p).app F).hom ≫
      (projectiveBundlePullbackCongr h).hom.app F ≫
      ((projectiveBundlePullbackComp p' g).app F).inv ≫
      (tensorPullback p').map a ≫ q).app O
      (((tensorPullback r).obj ((tensorPullback p).obj F)).presheaf.map
        (homOfLE hS).op
          (projectiveBundlePullbackSection r (projectiveBundlePullbackSection p x))) =
    L.presheaf.map (homOfLE hO).op
      (q.app (p' ⁻¹ᵁ W') (projectiveBundlePullbackSection p'
        (a.app W' (((tensorPullback g).obj F).presheaf.map (homOfLE hW).op
          (projectiveBundlePullbackSection g x))))) := by
  change q.app O (((tensorPullback p').map a).app O
    ((((projectiveBundlePullbackComp r p).app F).hom ≫
      (projectiveBundlePullbackCongr h).hom.app F ≫
      ((projectiveBundlePullbackComp p' g).app F).inv).app O _)) = _
  rw [section_square_restrict r p p' g h hW hO hS x]
  erw [Hom.app_presheaf_map, section_naturality, Hom.app_presheaf_map]

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
private theorem realization_generator_mem {B : Scheme.{u}} {F : B.Modules}
    (D : ProjectiveBundleRealization B F) (U : B.affineOpens) (x : Γ(F, U.1)) :
    D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x) ∈ D.A.data.grading U 1 := by
  apply (D.A.sectionEquiv_grade U 1 _).mp
  apply Submodule.subset_span
  exact ⟨fun _ ↦ x, by simp⟩

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
private theorem realization_chart_section {B : Scheme.{u}} {F : B.Modules}
    (D : ProjectiveBundleRealization B F) (U : B.affineOpens)
    (O : D.A.data.relProj.Opens) (hO : O ≤ D.A.data.relProjHom ⁻¹ᵁ U.1)
    (x : Γ(F, U.1)) :
    (D.twists.chart U).hom.app (D.A.data.relProjι U ⁻¹ᵁ O)
      (tensorPullbackSection (D.A.data.relProjι U) D.L O
        (D.L.presheaf.map (homOfLE hO).op
          (D.quotient.app (D.A.data.relProjHom ⁻¹ᵁ U.1)
            (projectiveBundlePullbackSection D.A.data.relProjHom x)))) =
      (Proj.unitToTwist (realization_generator_mem D U x)).app
        (D.A.data.relProjι U ⁻¹ᵁ O) (1 : Γ(Proj (D.A.data.grading U),
          D.A.data.relProjι U ⁻¹ᵁ O)) := by
  have h := D.quotient_generator U x (realization_generator_mem D U x)
  simp only [Adjunction.homEquiv_unit, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app] at h
  change (D.twists.chart U).hom.app _
    (projectiveBundlePullbackSection (D.A.data.relProjι U)
      (D.quotient.app _ (projectiveBundlePullbackSection D.A.data.relProjHom x))) = _ at h
  rw [projectiveBundlePullbackSection_eq_tensorPullbackSection] at h
  rw [ProjectiveBundleQuotientGeometry.tensor_section_res, Hom.app_presheaf_map, h]
  exact ProjectiveBundleQuotientGeometry.unit_section_res _ _

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
private theorem realization_chart_section_free {B : Scheme.{u}} {F : B.Modules}
    (D : ProjectiveBundleRealization B F) (U : B.affineOpens) (x : Γ(F, U.1))
    (O : D.A.data.relProj.Opens) (hO : O ≤ D.A.data.relProjHom ⁻¹ᵁ U.1)
    (hB : D.A.data.relProjι U ⁻¹ᵁ O ≤ Proj.basicOpen (D.A.data.grading U)
      (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x))) :
    IsFreeGenerator (D.L.presheaf.map (homOfLE hO).op
      (D.quotient.app (D.A.data.relProjHom ⁻¹ᵁ U.1)
        (projectiveBundlePullbackSection D.A.data.relProjHom x))) := by
  apply ProjectiveBundleQuotientGeometry.tensor_section_free_descent
    (D.A.data.relProjι U) D.L O (by
      rw [← D.A.data.relProjHom_preimage]
      exact hO)
  have H := (ProjectiveBundleQuotientGeometry.unit_section_res
    (Proj.unitToTwist (realization_generator_mem D U x)) hB) ▸
    ((Proj.isFreeGenerator_unitToTwist (realization_generator_mem D U x)).map hB)
  erw [← realization_chart_section D U O hO x] at H
  have H' := H.app_of_bijective (D.twists.chart U).inv
    (fun V _ ↦ ConcreteCategory.bijective_of_isIso _)
  simpa only [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app,
    ConcreteCategory.id_apply] using H'



set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
/-- On a fixed degree-one standard open the coherence-expanded target quotient image of
its pulled source generator is a free generator.

Source: Stacks Project, Tags 01NQ, 01NR and 01OB.
(blueprint: lem-pur-projective-bundle-realization-pullback-target-frame).

Proof: rewrite the pullback-composition comparisons on twice-pulled sections using their
adjunction-unit normalization. Naturality moves e.inv through the second pullback, so the
section in the target quotient is the pullback of e.inv applied to the restriction of g*x.
The equation hb identifies its symmetric degree-one image with b(x). Apply
D'.quotient_generator on the target affine chart; the chart sends the quotient section to
b(x)/1 in the degree-one twist. On D_+(b(x)) this section freely generates. Pullback along the
chart open immersion detects freeness, giving the assertion on its image in relative Proj.
This lemma concerns one specified generator, not transition or coefficient compatibility. -/
theorem projectiveBundleRealizationPullback_target_frame
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (b : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data)
    (hb : ∀ (U : B.affineOpens) (U' : B'.affineOpens) (h : U'.1 ≤ g ⁻¹ᵁ U.1)
      (x : F.val.obj (op U.1)),
      b.map h (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)) =
        D'.A.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
          (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op
            (projectiveBundlePullbackSection g x)))))
    (W : B.affineOpens) (W' : B'.affineOpens) (h : W'.1 ≤ g ⁻¹ᵁ W.1)
    (x : Γ(F, W.1)) :
    let M := (Scheme.Modules.tensorPullback b.relProjComparison).obj
      ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F)
    let q' :=
      ((projectiveBundlePullbackComp b.relProjComparison D.A.data.relProjHom).app F).hom ≫
        (projectiveBundlePullbackCongr b.isPullback.w).hom.app F ≫
        ((projectiveBundlePullbackComp D'.A.data.relProjHom g).app F).inv ≫
        (Scheme.Modules.tensorPullback D'.A.data.relProjHom).map e.inv ≫ D'.quotient
    let O := D'.A.data.relProjι W' ''ᵁ Proj.basicOpen (D'.A.data.grading W')
      (b.map h (D.A.sectionEquiv W (SymmetricAlgebra.ι _ _ x)))
    ∀ hO : O ≤ b.relProjComparison ⁻¹ᵁ (D.A.data.relProjHom ⁻¹ᵁ W.1),
      Scheme.Modules.IsFreeGenerator (q'.app O
        (M.presheaf.map (homOfLE hO).op
          (projectiveBundlePullbackSection b.relProjComparison
            (projectiveBundlePullbackSection D.A.data.relProjHom x)))) := by
  classical
  intro M q' O hO
  let y := e.inv.app W'.1
    (((tensorPullback g).obj F).presheaf.map (homOfLE h).op
      (projectiveBundlePullbackSection g x))
  have hbase : O ≤ D'.A.data.relProjHom ⁻¹ᵁ W'.1 := by
    rw [D'.A.data.relProjHom_preimage]
    exact (D'.A.data.relProjι W').image_le_opensRange _
  have hy : D'.A.data.relProjι W' ⁻¹ᵁ O ≤
      Proj.basicOpen (D'.A.data.grading W')
        (D'.A.sectionEquiv W' (SymmetricAlgebra.ι _ _ y)) := by
    rw [← hb W W' h x]
    exact le_of_eq ((D'.A.data.relProjι W').preimage_image_eq _)
  have H := realization_chart_section_free D' W' y O hbase hy
  have he := section_square_quotient b.relProjComparison D.A.data.relProjHom
    D'.A.data.relProjHom g b.isPullback.w e.inv D'.quotient h hbase hO x
  exact (congrArg IsFreeGenerator he).mpr H

end AlgebraicGeometry
