/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.Modules.LocalSectionOfEpi
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.Modules.HomSection

import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientEpi
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleSymmetricAlgebraIso
import WeilConjectures.AlgebraicGeometry.SymmetricProjSectionCompatibility
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

/-! # The complete flag bundle by tautological kernels

Source: Stacks Project, Chow Homology, Tag 02UL, proof of
`lemma-splitting-principle` (blueprint: def-pur-complete-flag-bundle).

`completeFlagBundle` is the rank recursion. Its levels are actual sheaves with maps to
its pulled-back module. `completeFlagStep` is the uniquely determined inclusion between
successive levels, and `completeFlagQuotient` is its sheaf cokernel.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject BigOperators

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback

/-- The universal property fixing a normalized quotient-line projectivization.
The line quotient is a sheaf epimorphism, and the comparison must carry the
prescribed universal quotient to that very quotient.
Source: Stacks, Tag 01OB (blueprint: def-pur-complete-flag-bundle). -/
def IsCompleteFlagProjectivization {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F) : Prop :=
  ∀ (S : Scheme.{u}) (f : S ⟶ T) (M : S.Modules) [M.IsInvertible]
    (ε : (Scheme.Modules.tensorPullback f).obj F ⟶ M) [Epi ε],
    ∃! g : S ⟶ D.A.data.relProj, ∃ h : g ≫ D.A.data.relProjHom = f,
      ∃ θ : (Scheme.Modules.tensorPullback g).obj D.L ≅ M,
        (Scheme.Modules.tensorPullback g).map D.quotient ≫ θ.hom =
          ((Scheme.Modules.tensorPullbackSectionComp g D.A.data.relProjHom).app F).inv ≫
            (projectiveBundlePullbackCongr h).hom.app F ≫ ε

section FlagProjectivization

open CategoryTheory.Functor

attribute [local implicit_reducible] Scheme.GradedAlgebraData.relProjFunctor

/- The normalized unit identifies the two pullback adjunction APIs. All following
comparison constructions use actual symmetric algebras and the existing quotient charts. -/

private theorem flag_adj_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.tensorPullbackSectionAdjunction f =
      projectiveBundlePullbackAdjunction f := by
  apply (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction f).unique
  · exact (Classical.choose_spec
      (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction f)).1
  · intro M V m
    exact Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction f) M
      (Opposite.op V) m

private theorem flag_conjugate_uniq {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R : D ⥤ C} (a : L₁ ⊣ R) (b : L₂ ⊣ R) :
    conjugateEquiv a b (a.leftAdjointUniq b).inv = 𝟙 _ := by
  change ((conjugateIsoEquiv a b)
    ((conjugateIsoEquiv a b).symm (Iso.refl R))).hom = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem flag_conjugate_uniq_hom {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R : D ⥤ C} (a : L₁ ⊣ R) (b : L₂ ⊣ R) :
    conjugateEquiv b a (a.leftAdjointUniq b).hom = 𝟙 _ :=
  flag_conjugate_uniq b a

private theorem flag_conjugate_right {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (e : R₁ ≅ R₂) :
    conjugateEquiv a b (b.leftAdjointUniq (a.ofNatIsoRight e)).hom = e.hom := by
  ext M
  simp only [conjugateEquiv_apply_app, Adjunction.unit_leftAdjointUniq_hom_app_assoc,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, id_obj, comp_obj,
    whiskerLeft_app, Category.assoc]
  rw [← e.hom.naturality, ← Category.assoc, a.right_triangle_components, Category.id_comp]

private theorem flag_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    projectiveBundlePullbackComp f g =
      (Scheme.Modules.tensorPullbackSectionComp f g).symm := by
  let ag := projectiveBundlePullbackAdjunction g
  let af := projectiveBundlePullbackAdjunction f
  let ac := projectiveBundlePullbackAdjunction (f ≫ g)
  let bg := Scheme.Modules.pullbackPushforwardAdjunction g
  let bf := Scheme.Modules.pullbackPushforwardAdjunction f
  let bc := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  have h : conjugateEquiv (ag.comp af) ac (projectiveBundlePullbackComp f g).inv =
      (Scheme.Modules.pushforwardComp f g).hom := by
    simp only [projectiveBundlePullbackComp, Iso.trans_inv, Iso.symm_inv,
      isoWhiskerRight_inv, isoWhiskerLeft_inv, Category.assoc]
    rw [← conjugateEquiv_comp (ag.comp af) bc ac,
      ← conjugateEquiv_comp (ag.comp af) (bg.comp bf) bc,
      ← conjugateEquiv_comp (ag.comp af) (bg.comp af) (bg.comp bf)]
    simp only [ag, af, ac, bg, bf, bc, projectiveBundlePullbackAdjunction,
      projectiveBundleTensorPullbackIso, conjugateEquiv_whiskerRight,
      conjugateEquiv_whiskerLeft, flag_conjugate_uniq, flag_conjugate_uniq_hom,
      Category.comp_id,
      Scheme.Modules.conjugateEquiv_pullbackComp_inv]
    ext M
    simp
  apply Iso.ext_inv
  apply (conjugateEquiv (ag.comp af) ac).injective
  rw [h]
  dsimp only [Iso.symm_inv]
  unfold Scheme.Modules.tensorPullbackSectionComp
  rw [flag_adj_eq, flag_adj_eq, flag_adj_eq]
  exact (flag_conjugate_right (ag.comp af) ac (Scheme.Modules.pushforwardComp f g)).symm

private theorem flag_section_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (m : Γ(M, U)) :
    projectiveBundlePullbackSection f m = Scheme.Modules.tensorPullbackSection f M U m := by
  unfold projectiveBundlePullbackSection
  rw [← flag_adj_eq]
  exact (Classical.choose_spec
    (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction f)).1 M U m

private theorem flag_unit_section {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (projectiveBundlePullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
      (projectiveBundlePullbackSection f (M := Scheme.Modules.unit Y)
        (U := U) (1 : Γ(Y, U))) = (1 : Γ(X, f ⁻¹ᵁ U)) := by
  have h := (projectiveBundlePullbackAdjunction f).unit_leftAdjointUniq_hom_app
    (Scheme.Modules.pullbackPushforwardAdjunction f) (Scheme.Modules.unit Y)
  have hs := congrArg (fun k ↦ k.app U (1 : Γ(Y, U))) h
  dsimp only [projectiveBundlePullbackUnitIso, Iso.trans_hom]
  change (Scheme.Modules.pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ U)
    ((projectiveBundleTensorPullbackIso f).hom.app (Scheme.Modules.unit Y) |>.app (f ⁻¹ᵁ U)
      (projectiveBundlePullbackSection f (M := Scheme.Modules.unit Y) (U := U) (1 : Γ(Y, U)))) = _
  change ((projectiveBundleTensorPullbackIso f).hom.app (Scheme.Modules.unit Y)).app
      (f ⁻¹ᵁ U) (projectiveBundlePullbackSection f (M := Scheme.Modules.unit Y)
        (U := U) (1 : Γ(Y, U))) =
    Scheme.Modules.pullbackSection f (M := Scheme.Modules.unit Y) (U := U) (1 : Γ(Y, U)) at hs
  rw [hs, Scheme.Modules.pullbackObjUnitIso_hom_app_pullbackSection, map_one]

private noncomputable def flag_canonical_algebra {T : Scheme.{u}} (F : T.Modules)
    [F.IsQuasicoherent] : T.SymmetricGradedAlgebraData F where
  data := SymmetricAlgebraSheaf.gradedAlgebraData F
  sectionEquiv U := AlgEquiv.refl
  sectionEquiv_grade U d x := by
    rw [projectiveBundleSymmetricDegree_eq]
    rfl
  sectionEquiv_restriction h x := rfl

attribute [local irreducible] Scheme.Modules.tensorPullbackSectionComp projectiveBundlePullbackComp
  projectiveBundlePullbackSection projectiveBundleTensorPullbackIso
  projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  Scheme.Modules.tensorPullbackObj Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.Modules.tensorPullbackSection Scheme.GradedAlgebraData.relProj
  Scheme.GradedAlgebraData.relProjι

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem flag_comparison_iso {C : Type u} [Category C]
    {A B D F G : C} (e : A ≅ B) (r : A ≅ D) (s : D ≅ F) (t : F ≅ G) :
    ∃ c : B ≅ G, e.hom ≫ c.hom = r.hom ≫ s.hom ≫ t.hom := by
  refine ⟨e.symm ≪≫ r ≪≫ s ≪≫ t, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

private theorem flag_affine_comparison_exists {T : Scheme.{u}} (F : T.Modules)
    [F.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient F)
    (U V : T.affineOpens) (h : U ≤ V) :
    Nonempty (SymmetricProjTautologicalCharts.AffineComparison F D U V h) := by
  obtain ⟨c, hc⟩ := flag_comparison_iso
    ((Scheme.Modules.tensorPullback
      ((SymmetricAlgebraSheaf.gradedAlgebraData F).relProjFunctor.map (homOfLE h))).mapIso
        (D.chart V))
    (((Scheme.Modules.tensorPullbackSectionComp
      ((SymmetricAlgebraSheaf.gradedAlgebraData F).relProjFunctor.map (homOfLE h))
      ((SymmetricAlgebraSheaf.gradedAlgebraData F).relProjι V)).app D.line).symm)
    (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj D.line)
      ((SymmetricAlgebraSheaf.gradedAlgebraData F).relProjFunctor_map_relProjι
        (homOfLE h)))) (D.chart U)
  exact ⟨⟨c, hc⟩⟩

private noncomputable def flag_affine_comparison {T : Scheme.{u}} (F : T.Modules)
    [F.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient F)
    (U V : T.affineOpens) (h : U ≤ V) :
    SymmetricProjTautologicalCharts.AffineComparison F D U V h :=
  Classical.choice (flag_affine_comparison_exists F D U V h)

private theorem flag_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) :
    (projectiveBundlePullbackCongr h).hom.app M =
      (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj M) h)).hom := by
  subst g
  rfl

private theorem flag_hom_comp_apply {X : Scheme.{u}} {M N P : X.Modules}
    (a : M ⟶ N) (b : N ⟶ P) (U : X.Opens) (s : Γ(M, U)) :
    (a ≫ b).app U s = b.app U (a.app U s) :=
  congrArg (fun k ↦ k s) (Scheme.Modules.Hom.comp_app (U := U) a b)

private theorem flag_section_natural {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (a : M ⟶ N) (U : Y.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.tensorPullback f).map a).app (f ⁻¹ᵁ U)
      (projectiveBundlePullbackSection f m) =
        projectiveBundlePullbackSection f (a.app U m) := by
  unfold projectiveBundlePullbackSection
  exact congrArg (fun k ↦ k.app U m)
    ((projectiveBundlePullbackAdjunction f).unit_naturality a)

private theorem flag_generator_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    {LV : Y.Modules} {LU : X.Modules} (tV : Scheme.Modules.unit Y ⟶ LV)
    (tU : Scheme.Modules.unit X ⟶ LU)
    (c : (Scheme.Modules.tensorPullback f).obj LV ⟶ LU)
    (h : (Scheme.Modules.tensorPullback f).map tV ≫ c =
      (projectiveBundlePullbackUnitIso f).hom ≫ tU) :
    c.app (f ⁻¹ᵁ ⊤) (projectiveBundlePullbackSection f
      (tV.app ⊤ (1 : Γ(Y, ⊤)))) = tU.app (f ⁻¹ᵁ ⊤) (1 : Γ(X, f ⁻¹ᵁ ⊤)) := by
  have hv := congrArg (fun k ↦ k.app (f ⁻¹ᵁ ⊤)
    (projectiveBundlePullbackSection f (M := Scheme.Modules.unit Y) (U := ⊤)
      (1 : Γ(Y, ⊤)))) h
  simp only [flag_hom_comp_apply] at hv
  have hn := flag_section_natural f tV ⊤ (1 : Γ(Y, ⊤))
  have hu := flag_unit_section f ⊤
  exact (congrArg (fun z ↦ c.app (f ⁻¹ᵁ ⊤) z) hn).symm.trans
    (hv.trans (congrArg (fun z ↦ tU.app (f ⁻¹ᵁ ⊤) z) hu))

private theorem flag_quotient_transport {T P S : Scheme.{u}}
    (g : S ⟶ P) (p : P ⟶ T) (f : S ⟶ T) (h : g ≫ p = f)
    (F : T.Modules) (L : P.Modules)
    (q : (Scheme.Modules.tensorPullback p).obj F ⟶ L)
    (M : S.Modules) (θ : (Scheme.Modules.tensorPullback g).obj L ≅ M)
    (ε : (Scheme.Modules.tensorPullback f).obj F ⟶ M) :
    ((eqToIso (congrArg (fun t ↦ (Scheme.Modules.tensorPullback t).obj F) h)).inv ≫
        (Scheme.Modules.tensorPullbackSectionComp g p).hom.app F ≫
        (Scheme.Modules.tensorPullback g).map q) ≫ θ.hom = ε ↔
      (Scheme.Modules.tensorPullback g).map q ≫ θ.hom =
        ((Scheme.Modules.tensorPullbackSectionComp g p).app F).inv ≫
          (projectiveBundlePullbackCongr h).hom.app F ≫ ε := by
  simp only [Category.assoc, flag_congr_hom]
  rw [Iso.inv_comp_eq]
  exact ((Scheme.Modules.tensorPullbackSectionComp g p).app F).eq_inv_comp.symm

private theorem flag_universal_from_normalized {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F)
    (hu : ∀ (S : Scheme.{u}) (f : S ⟶ T) (M : S.Modules) [M.IsInvertible]
      (ε : (Scheme.Modules.tensorPullback f).obj F ⟶ M) [Epi ε],
      ∃! g : S ⟶ D.A.data.relProj, ∃ h : g ≫ D.A.data.relProjHom = f,
        ∃ θ : (Scheme.Modules.tensorPullback g).obj D.L ≅ M,
          ((eqToIso (congrArg (fun t ↦ (Scheme.Modules.tensorPullback t).obj F) h)).inv ≫
            (Scheme.Modules.tensorPullbackSectionComp g D.A.data.relProjHom).hom.app F ≫
            (Scheme.Modules.tensorPullback g).map D.quotient) ≫ θ.hom = ε) :
    IsCompleteFlagProjectivization D := by
  intro S f M hM ε hε
  obtain ⟨g, ⟨h, θ, hθ⟩, hg⟩ := @hu S f M hM ε hε
  refine ⟨g, ⟨h, θ, ?_⟩, ?_⟩
  · exact (flag_quotient_transport g D.A.data.relProjHom f h F D.L D.quotient M θ ε).mp hθ
  · rintro a ⟨ha, v, hv⟩
    apply hg a
    refine ⟨ha, v, ?_⟩
    exact (flag_quotient_transport a D.A.data.relProjHom f ha F D.L D.quotient M v ε).mpr hv

attribute [local irreducible] Proj.twist Proj.unitToTwist
  IsCompleteFlagProjectivization

/- Reuse the constructor's exact dependent premise, including its scalar-module
instances, instead of elaborating another presentation of the same equation. -/
private def flag_premise {P : Prop} {α : Sort*} (_ : P → α) : Prop := P

/- Naming this constructor application keeps its fields shared while the universal
property is checked. All of the data and its generator equation are supplied. -/
private noncomputable def flag_realization {T : Scheme.{u}} (F : T.Modules)
    (A : T.SymmetricGradedAlgebraData F) (L : A.data.relProj.Modules)
    (q : (Scheme.Modules.tensorPullback A.data.relProjHom).obj F ⟶ L)
    (twists : TautologicalTwistData T A.data L)
    (hgen : flag_premise (@ProjectiveBundleRealization.mk T F A L q twists)) :
    ProjectiveBundleRealization T F :=
  @ProjectiveBundleRealization.mk T F A L q twists hgen

attribute [local irreducible] flag_realization

private theorem flag_exists_from_normalized_data {T : Scheme.{u}} (F : T.Modules)
    (A : T.SymmetricGradedAlgebraData F) (L : A.data.relProj.Modules)
    (q : (Scheme.Modules.tensorPullback A.data.relProjHom).obj F ⟶ L)
    (twists : TautologicalTwistData T A.data L)
    (hgen : flag_premise (@ProjectiveBundleRealization.mk T F A L q twists))
    (hu : flag_premise (flag_universal_from_normalized
      (flag_realization F A L q twists hgen))) :
    ∃ D : ProjectiveBundleRealization T F, IsCompleteFlagProjectivization D := by
  exact ⟨flag_realization F A L q twists hgen,
    flag_universal_from_normalized (flag_realization F A L q twists hgen) hu⟩

private theorem flag_normalized_unit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.boundaryPullbackComparison f).app (Scheme.Modules.unit Y) ≪≫
        Scheme.Modules.pullbackObjUnitIso f = projectiveBundlePullbackUnitIso f := by
  unfold Scheme.Modules.boundaryPullbackComparison projectiveBundlePullbackUnitIso
    projectiveBundleTensorPullbackIso
  rfl

private theorem flag_generator_transport_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    {LV : Y.Modules} {LU : X.Modules} (tV : Scheme.Modules.unit Y ⟶ LV)
    (tU : Scheme.Modules.unit X ⟶ LU)
    (c : (Scheme.Modules.tensorPullback f).obj LV ⟶ LU)
    (h : (Scheme.Modules.tensorPullback f).map tV ≫ c =
      ((Scheme.Modules.boundaryPullbackComparison f).app (Scheme.Modules.unit Y) ≪≫
        Scheme.Modules.pullbackObjUnitIso f).hom ≫ tU) :
    c.app (f ⁻¹ᵁ ⊤) (projectiveBundlePullbackSection f
      (tV.app ⊤ (1 : Γ(Y, ⊤)))) = tU.app (f ⁻¹ᵁ ⊤) (1 : Γ(X, f ⁻¹ᵁ ⊤)) := by
  apply flag_generator_transport f tV tU c
  exact h.trans (congrArg (fun e ↦ e.hom ≫ tU) (flag_normalized_unit_eq f))

private theorem flag_transport_normalized {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (j : X ⟶ Z) (h : f ≫ g = j) (L : Z.Modules) :
    (projectiveBundlePullbackComp f g).app L ≪≫
        (projectiveBundlePullbackCongr h).app L =
      ((Scheme.Modules.tensorPullbackSectionComp f g).symm.app L) ≪≫
        eqToIso (congrArg (fun t ↦ (Scheme.Modules.tensorPullback t).obj L) h) := by
  subst j
  exact congrArg (fun e ↦ e.app L ≪≫ Iso.refl _) (flag_comp_eq f g)

private theorem flag_chart_overlap {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (j : X ⟶ Z) (h : f ≫ g = j) (L : Z.Modules)
    {LV : Y.Modules} {LU : X.Modules}
    (eV : (Scheme.Modules.tensorPullback g).obj L ≅ LV)
    (eU : (Scheme.Modules.tensorPullback j).obj L ≅ LU)
    (c : (Scheme.Modules.tensorPullback f).obj LV ≅ LU)
    (hc : (Scheme.Modules.tensorPullback f).map eV.hom ≫ c.hom =
      (Scheme.Modules.tensorPullbackSectionComp f g).inv.app L ≫
        (eqToIso (congrArg (fun t ↦ (Scheme.Modules.tensorPullback t).obj L) h)).hom ≫
          eU.hom) :
    ((projectiveBundlePullbackComp f g).app L ≪≫
      (projectiveBundlePullbackCongr h).app L) ≪≫ eU =
        (Scheme.Modules.tensorPullback f).mapIso eV ≪≫ c := by
  apply Iso.ext
  have he := congrArg (fun e ↦ (e ≪≫ eU).hom)
    (flag_transport_normalized f g j h L)
  apply he.trans
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_inv, Functor.comp_obj]
  exact (Category.assoc _ _ _).trans hc.symm

private theorem flag_adjoint_generator_eq {S P X : Scheme.{u}}
    (p : P ⟶ S) (j : X ⟶ P) (F : S.Modules) (L : P.Modules)
    (q : (Scheme.Modules.tensorPullback p).obj F ⟶ L) (U : S.Opens) (m : Γ(F, U)) :
    projectiveBundlePullbackSection j
      (((projectiveBundlePullbackAdjunction p).homEquiv F L q).app U m) =
    Scheme.Modules.tensorPullbackSection j L (p ⁻¹ᵁ U)
      (((Scheme.Modules.tensorPullbackSectionAdjunction p).homEquiv F L q).app U m) := by
  have he := congrArg (fun adj ↦ (adj.homEquiv F L q).app U m) (flag_adj_eq p)
  exact (flag_section_eq j L (p ⁻¹ᵁ U) _).trans
    (congrArg (Scheme.Modules.tensorPullbackSection j L (p ⁻¹ᵁ U)) he.symm)

section FlagChartConstruction

attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory TopCat.Sheaf
attribute [local irreducible] Scheme.Modules.boundaryPullbackComparison

private theorem flag_twists_of_charts_exists {T : Scheme.{u}}
    (A : T.GradedAlgebraData) (L : A.relProj.Modules)
    (chart : ∀ U : T.affineOpens,
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅ Proj.twist (A.grading U) 1)
    (c : ∀ {U V : T.affineOpens} (h : U ≤ V),
      (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).obj
        (Proj.twist (A.grading V) 1) ≅ Proj.twist (A.grading U) 1)
    (hc : ∀ {U V : T.affineOpens} (h : U ≤ V),
      (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).map
        (chart V).hom ≫ (c h).hom =
      (Scheme.Modules.tensorPullbackSectionComp (A.relProjFunctor.map (homOfLE h))
        (A.relProjι V)).inv.app L ≫
      (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj L)
        (A.relProjFunctor_map_relProjι (homOfLE h)))).hom ≫ (chart U).hom)
    (hs : ∀ {U V : T.affineOpens} (h : U ≤ V) (a : A.obj V)
      (ha : a ∈ A.grading V 1),
      (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).map
        (Proj.unitToTwist ha) ≫ (c h).hom =
      ((Scheme.Modules.boundaryPullbackComparison (A.relProjFunctor.map (homOfLE h))).app
        (Scheme.Modules.unit _) ≪≫
          Scheme.Modules.pullbackObjUnitIso (A.relProjFunctor.map (homOfLE h))).hom ≫
        Proj.unitToTwist (A.res h |>.map_mem ha)) :
    ∃ t : TautologicalTwistData T A L,
      t.chart = chart ∧ @t.twistRestriction = @c := by
  refine ⟨{
    chart := chart
    twistRestriction := c
    restriction_generator := ?_
    chart_overlap := ?_ }, rfl, rfl⟩
  · intro U V h a ha
    exact @flag_generator_transport_normalized (A.relProjFunctor.obj U) (A.relProjFunctor.obj V)
      (A.relProjFunctor.map (homOfLE h)) (Proj.twist (A.grading V) 1)
      (Proj.twist (A.grading U) 1) (Proj.unitToTwist ha)
      (Proj.unitToTwist (A.res h |>.map_mem ha)) (c h).hom (hs h a ha)
  · intro U V h
    exact @flag_chart_overlap (A.relProjFunctor.obj U) (A.relProjFunctor.obj V) A.relProj
      (A.relProjFunctor.map (homOfLE h)) (A.relProjι V) (A.relProjι U)
      (A.relProjFunctor_map_relProjι (homOfLE h)) L _ _ (chart V) (chart U) (c h) (hc h)

private theorem flag_canonical_twists_exists {T : Scheme.{u}} (F : T.Modules)
    [F.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient F) :
    ∃ t : TautologicalTwistData T (SymmetricAlgebraSheaf.gradedAlgebraData F) D.line,
      t.chart = D.chart := by
  obtain ⟨t, ht, _⟩ := flag_twists_of_charts_exists _ D.line D.chart
    (fun {U V} h ↦ (flag_affine_comparison F D U V h).comparison)
    (fun {U V} h ↦ (flag_affine_comparison F D U V h).chart_compatibility)
    (fun {U V} h a ha ↦
      SymmetricProjTautologicalCharts.section_compatibility_of_affine_comparison
        F D U V h (flag_affine_comparison F D U V h) a ha)
  exact ⟨t, ht⟩

end FlagChartConstruction

private theorem flag_canonical_generator {T : Scheme.{u}} (F : T.Modules)
    [F.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient F)
    (twists : TautologicalTwistData T (SymmetricAlgebraSheaf.gradedAlgebraData F) D.line)
    (hchart : twists.chart = D.chart) :
    flag_premise (@ProjectiveBundleRealization.mk T F (flag_canonical_algebra F)
      D.line D.quotient twists) := by
  intro U m hm
  change (twists.chart U).hom.app _ _ = _
  rw [hchart]
  exact (congrArg ((D.chart U).hom.app _)
    (flag_adjoint_generator_eq (SymmetricAlgebraSheaf.gradedAlgebraData F).relProjHom
      ((SymmetricAlgebraSheaf.gradedAlgebraData F).relProjι U) F D.line D.quotient
      U.1 m)).trans (D.generator U m hm)

set_option maxHeartbeats 1000000 in
-- Kernel conversion expands the canonical relative-Proj quotient classification.
private theorem flag_canonical_universal {T : Scheme.{u}} (F : T.Modules)
    [F.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient F)
    (twists : TautologicalTwistData T (SymmetricAlgebraSheaf.gradedAlgebraData F) D.line)
    (hgen : flag_premise (@ProjectiveBundleRealization.mk T F (flag_canonical_algebra F)
      D.line D.quotient twists))
    (hu : ∀ (S : Scheme.{u}) (f : S ⟶ T) (M : S.Modules)
      (ε : (Scheme.Modules.tensorPullback f).obj F ⟶ M), M.IsInvertible → Epi ε →
        ∃! g : S ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData F).relProj,
          ProjectiveBundleQuotientGeometry.Classifies D f M ε g) :
    flag_premise (flag_universal_from_normalized
      (flag_realization F (flag_canonical_algebra F) D.line D.quotient twists hgen)) := by
  intro S f M hM ε hε
  delta flag_realization
  exact hu S f M ε hM hε

set_option maxHeartbeats 1000000 in
-- Assembly checks dependent projections of the canonical relative-Proj realization.
/-- The normalized symmetric-algebra projectivization has its quotient-line universal
property, which determines the scheme and quotient up to canonical isomorphism.
Source: Stacks, Tags 01OB and 01OE (blueprint: def-pur-complete-flag-bundle).
Proof: `projective_bundle_quotient_geometry` gives, for the actual symmetric algebra of
`F`, a tautological quotient `q*F → L` with affine charts `L|_{q⁻¹U} ≅ O(1)` and its
quotient-classifying universal property. Restricting the charts along inclusions of
affine opens gives the twist restrictions, and the section compatibility of
`lem-trf-symmetric-proj-section-compatibility` carries degree-one generators to
generators; this is the twist data of a realization. Its generator equation is the
chart equation of the tautological quotient, after identifying the two pullback
adjunctions, which have the same normalized unit. The same identification turns their
composition comparisons into each other (mate equivalence), so the classifying property
is exactly `IsCompleteFlagProjectivization`. -/
theorem exists_completeFlagProjectivization (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    ∃ D : ProjectiveBundleRealization T F, IsCompleteFlagProjectivization D := by
  have hLF : SheafOfModules.IsLocallyFree (R := T.ringCatSheaf) F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree F (n + 1)
  have hQC : SheafOfModules.IsQuasicoherent (R := T.ringCatSheaf) F :=
    SheafOfModules.instIsQuasicoherentOfIsLocallyFree F
  obtain ⟨D, _, hu, _⟩ :=
    ProjectiveBundleQuotientGeometry.projective_bundle_quotient_geometry T F
  obtain ⟨twists, hchart⟩ := flag_canonical_twists_exists F D
  exact flag_exists_from_normalized_data F (flag_canonical_algebra F) D.line D.quotient
    twists (flag_canonical_generator F D twists hchart)
    (flag_canonical_universal F D twists (flag_canonical_generator F D twists hchart) hu)

end FlagProjectivization

/-- A representative of the universal, normalized projectivization of the actual
symmetric algebra. The existence theorem specifies its universal property, while
`ProjectiveBundleRealization` fixes the affine algebras, restrictions, twist and
quotient by their homogeneous-localization formulas. Its data are determined up
to the canonical isomorphism used in interpreting the construction.
Source: Stacks, Tags 01OB, 01NR, 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagProjectivization (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    ProjectiveBundleRealization T F :=
  Classical.choose (exists_completeFlagProjectivization T n F)

attribute [local irreducible] completeFlagProjectivization CategoryTheory.Limits.limit
  CategoryTheory.Limits.colimit

/-- The tautological kernel is the categorical kernel in sheaves of modules, hence
is the subsheaf of sections annihilated by the prescribed quotient.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagKernel (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    (completeFlagProjectivization T n F).A.data.relProj.Modules :=
  kernel (completeFlagProjectivization T n F).quotient

private theorem kernel_basis {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {ι : Type*} [Finite ι]
    (v : Module.Basis ι R M) (f : M →ₗ[R] N) (τ : N)
    (hτ : Function.Injective fun r : R ↦ r • τ)
    (j : ι) (a : ι → R) (hj : a j = 1) (hε : ∀ i, f (v i) = a i • τ) :
    ∃ b : Module.Basis {i : ι // i ≠ j} R f.ker,
      ∀ i, (b i).val = v i.val - a i.val • v j := by
  classical
  let := Fintype.ofFinite ι
  let w (i : {i : ι // i ≠ j}) : f.ker :=
    ⟨v i.val - a i.val • v j, by simp [map_sub, map_smul, hε, hj]⟩
  let c : f.ker →ₗ[R] ({i : ι // i ≠ j} → R) :=
    LinearMap.pi fun i ↦ (v.coord i.val).comp f.ker.subtype
  have hc (x : f.ker) (i : {i : ι // i ≠ j}) : c x i = v.repr x.val i.val := rfl
  have hw (i k : {i : ι // i ≠ j}) : c (w i) k = if i = k then 1 else 0 := by
    simp [hc, w, map_sub, map_smul, Module.Basis.repr_self, k.property,
      Subtype.ext_iff, Finsupp.single_apply]
  have hinj : Function.Injective c := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro x hx
      have hx' : c x = 0 := hx
      have hz (i : ι) (hi : i ≠ j) : v.repr x.val i = 0 := by
        exact congrFun hx' ⟨i, hi⟩
      have he : x.val = v.repr x.val j • v j := by
        conv_lhs => rw [← v.sum_repr x.val]
        exact Finset.sum_eq_single j (fun i _ hi ↦ by rw [hz i hi, zero_smul])
          (by simp)
      have hj0 : v.repr x.val j = 0 := hτ (by
        have h : f x.val = 0 := x.property
        rw [he, map_smul, hε, hj, one_smul] at h
        simpa using h)
      apply Subtype.ext
      change x.val = 0
      rw [he, hj0, zero_smul]
    · exact bot_le
  have hsurj : Function.Surjective c := by
    intro t
    refine ⟨∑ i, t i • w i, ?_⟩
    ext k
    simp [map_sum, map_smul, hw]
  let e := LinearEquiv.ofBijective c ⟨hinj, hsurj⟩
  refine ⟨Module.Basis.ofEquivFun e, ?_⟩
  intro i
  have he : (Module.Basis.ofEquivFun e) i = w i := by
    apply hinj
    change e ((Module.Basis.ofEquivFun e) i) = c (w i)
    rw [Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
    ext k
    simp [hw, Pi.single_apply, eq_comm]
  rw [he]

/-- The explicit chart splitting and kernel basis. On `D₊(Xⱼ)` take `aᵢ=Xᵢ/Xⱼ`,
`v` the pulled-back frame and `τ=τⱼ`; the normalized quotient and its overlap
formulas are those of `ProjectiveBundleRealization` and `ProjectiveBundleFrameChart`.
Source: Stacks, Tags 01OB and 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: every section of the line is uniquely a multiple of `τ`. Send that multiple
to the same multiple of `vⱼ`. Since `aⱼ=1`, this is a section of the quotient.
For a kernel vector subtract the sum of its coefficients away from j times
`vᵢ-aᵢvⱼ`. The result is a multiple of `vⱼ` in the kernel, hence zero because
`τ` is a free generator. The coefficients away from j also prove independence.
Sections of the sheaf kernel are precisely the sectionwise kernel, since the
sections functor preserves limits. This identifies the displayed basis with
sections of the actual sheaf kernel, on every further open in the chart. -/
theorem completeFlagKernel_chart {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F) (r : ℕ)
    (W : D.A.data.relProj.Opens)
    (v : Module.Basis (Fin r) Γ(D.A.data.relProj, W)
      Γ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F, W))
    (τ : Γ(D.L, W)) (hτ : Scheme.Modules.IsFreeGenerator τ)
    (j : Fin r) (a : Fin r → Γ(D.A.data.relProj, W)) (hj : a j = 1)
    (hε : ∀ i : Fin r, Scheme.Modules.Hom.app D.quotient W (v i) = a i • τ) :
    (∃ s : Γ(D.L, W) →ₗ[Γ(D.A.data.relProj, W)]
        Γ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F, W),
      s τ = v j ∧ ∀ x : Γ(D.L, W), Scheme.Modules.Hom.app D.quotient W (s x) = x) ∧
    ∃ b : Module.Basis {i : Fin r // i ≠ j} Γ(D.A.data.relProj, W)
        Γ(kernel D.quotient, W),
      ∀ i : {i : Fin r // i ≠ j},
        Scheme.Modules.Hom.app (kernel.ι D.quotient) W (b i) = v i.1 - a i.1 • v j := by
  classical
  constructor
  · let s : Γ(D.L, W) →ₗ[Γ(D.A.data.relProj, W)]
        Γ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F, W) :=
      { toFun := fun x ↦ hτ.coeff x • v j
        map_add' := by intro x y; simp [add_smul]
        map_smul' := by intro c x; simp [mul_smul] }
    refine ⟨s, ?_, ?_⟩
    · have hc : hτ.coeff τ = 1 := by simpa using hτ.coeff_smul_self 1
      simp [s, hc]
    · intro x
      simp [s, hε, hj]
  · let E := SheafOfModules.evaluation D.A.data.relProj.ringCatSheaf (Opposite.op W)
    let e := PreservesKernel.iso E D.quotient ≪≫ ModuleCat.kernelIsoKer (E.map D.quotient)
    have he : e.hom ≫ ModuleCat.ofHom (E.map D.quotient).hom.ker.subtype =
        E.map (kernel.ι D.quotient) := by
      simp [e, PreservesKernel.iso_hom]
    obtain ⟨b, hb⟩ := kernel_basis v (D.quotient.val.app (Opposite.op W)).hom
      τ hτ.smul_left_injective j a hj hε
    refine ⟨b.map e.symm.toLinearEquiv, ?_⟩
    intro i
    change (E.map (kernel.ι D.quotient)) (e.inv (b i)) = _
    rw [← he]
    change (e.hom (e.inv (b i))).val = _
    simp only [Iso.inv_hom_id_apply]
    exact hb i

private theorem realization_generator_mem {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F) (U : T.affineOpens) (m : Γ(F, U.1)) :
    D.A.sectionEquiv U (SymmetricAlgebra.ι Γ(T, U.1) Γ(F, U.1) m) ∈
      D.A.data.grading U 1 := by
  apply (D.A.sectionEquiv_grade U 1 _).mp
  apply Submodule.subset_span
  exact ⟨fun _ ↦ m, by simp; rfl⟩

private theorem realization_chart_cover {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F) (U : T.affineOpens) :
    (⨆ m : Γ(F, U.1), Proj.basicOpen (D.A.data.grading U)
      (D.A.sectionEquiv U (SymmetricAlgebra.ι Γ(T, U.1) Γ(F, U.1) m))) = ⊤ := by
  let A := D.A.data
  let : GradedAlgebra (A.grading U) := A.gradedAlgebra U
  let a (m : Γ(F, U.1)) := D.A.sectionEquiv U (SymmetricAlgebra.ι Γ(T, U.1) Γ(F, U.1) m)
  apply Proj.iSup_basicOpen_eq_top' (A.grading U) a
    (fun m ↦ ⟨1, realization_generator_mem D U m⟩)
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨y, rfl⟩ := (D.A.sectionEquiv U).surjective x
  induction y using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [(D.A.sectionEquiv U).commutes]
    exact (Algebra.adjoin (A.grading U 0) (Set.range a)).algebraMap_mem
      (algebraMap Γ(T, U.1) (A.grading U 0) r)
  | ι m => exact Algebra.subset_adjoin ⟨m, rfl⟩
  | mul a b ha hb => simpa only [map_mul] using mul_mem ha hb
  | add a b ha hb => simpa only [map_add] using add_mem ha hb

private theorem realization_line_invertible {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F) : D.L.IsInvertible := by
  have hlocal (U : T.affineOpens) :
      ((Scheme.Modules.pullback (D.A.data.relProjι U)).obj D.L).IsInvertible := by
    have := Proj.isInvertible_twist (D.A.data.grading U) 1 (by
      intro x
      obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((realization_chart_cover D U).ge (Set.mem_univ x))
      exact ⟨_, realization_generator_mem D U m, hm⟩)
    exact Scheme.Modules.IsInvertible.of_iso ((D.twists.chart U).symm ≪≫
      (projectiveBundleTensorPullbackIso (D.A.data.relProjι U)).app D.L)
  have hfree := Scheme.Modules.isFiniteLocallyFreeOfRank_of_isOpenImmersion D.L (r := 1)
    D.A.data.relProjι D.A.data.iSup_opensRange_relProjι (fun U ↦ by
      have := hlocal U
      exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
        ((Scheme.Modules.pullback (D.A.data.relProjι U)).obj D.L)).mp
        (Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
          ((Scheme.Modules.pullback (D.A.data.relProjι U)).obj D.L)))
  have : SheafOfModules.IsInvertible.{u, u, u} D.L :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one D.L).mpr hfree
  exact Scheme.Modules.IsInvertible.of_sheafOfModules D.L

private theorem realization_quotient_epi {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F) : Epi D.quotient :=
  projectiveBundleQuotient_epi D

/-- The tautological quotient is locally split, and its displayed local splittings
remain splittings after every pullback. This asserts no global splitting.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: the opens `D₊(m)` for degree-one generators `m` cover each affine Proj, and the
twist is free on `m` there, so the line `L` is invertible; the quotient is epi by
`projectiveBundleQuotient_epi`. Pullback along `g` is a left adjoint, so it keeps the
quotient epi and the line invertible. An epimorphism onto a finite locally free module
has sections locally; transport these sections from pullback along an open immersion
to restriction. -/
theorem completeFlagKernel_pullback_locally_split (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)]
    (S : Scheme.{u}) (g : S ⟶ (completeFlagProjectivization T n F).A.data.relProj) :
    ∀ x : S, ∃ W : S.Opens, x ∈ W ∧
      ∃ s : (Scheme.Modules.tensorPullback W.ι).obj
          ((Scheme.Modules.tensorPullback g).obj (completeFlagProjectivization T n F).L) ⟶
        (Scheme.Modules.tensorPullback W.ι).obj
          ((Scheme.Modules.tensorPullback g).obj
            ((Scheme.Modules.tensorPullback
              (completeFlagProjectivization T n F).A.data.relProjHom).obj F)),
        s ≫ (Scheme.Modules.tensorPullback W.ι).map
          ((Scheme.Modules.tensorPullback g).map
            (completeFlagProjectivization T n F).quotient) = 𝟙 _ := by
  let D := completeFlagProjectivization T n F
  let H := Scheme.Modules.tensorPullback g
  have : D.L.IsInvertible := realization_line_invertible D
  have : Epi D.quotient := realization_quotient_epi D
  have : H.IsLeftAdjoint := (Scheme.Modules.tensorPullbackSectionAdjunction g).isLeftAdjoint
  have : Epi (H.map D.quotient) := inferInstance
  have : (H.obj D.L).IsInvertible := Scheme.Modules.IsInvertible.of_iso
    ((projectiveBundleTensorPullbackIso g).app D.L).symm
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (H.obj D.L)
  have : (H.obj D.L).IsFiniteLocallyFreeOfRank 1 :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (H.obj D.L)).mp
      inferInstance
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (H.obj D.L) 1
  intro x
  obtain ⟨U, hx, s, hs⟩ := Scheme.Modules.exists_local_section_of_epi (H.map D.quotient) x
  let a : Scheme.Modules.tensorPullback U.ι ≅ Scheme.Modules.restrictFunctor U.ι :=
    projectiveBundleTensorPullbackIso U.ι ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  refine ⟨U, hx, a.hom.app _ ≫ s ≫ a.inv.app _, ?_⟩
  rw [Category.assoc, Category.assoc, ← a.inv.naturality,
    ← Category.assoc s, hs, Category.id_comp, a.hom_inv_id_app]

private theorem flag_cokernel_rank_of_split
    {Z : Scheme.{u}} {M N : Z.Modules} (f : M ⟶ N) (k b : ℕ)
    [M.IsFiniteLocallyFreeOfRank b] [N.IsFiniteLocallyFreeOfRank k] [IsSplitMono f] :
    (cokernel f).IsFiniteLocallyFreeOfRank (k - b) := by
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree M b
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree N k
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N k
  have := Scheme.Modules.isQuasicoherent_cokernel (X := Z) f
  let T := ShortComplex.cokernelSequence f
  let t := ShortComplex.Splitting.ofExactOfRetraction T
    (ShortComplex.cokernelSequence_exact f) (retraction f) (IsSplitMono.id f)
    (by dsimp [T, ShortComplex.cokernelSequence]; infer_instance)
  apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_isAffineOpen
  intro U hU
  obtain ⟨hfp, hproj⟩ := Scheme.Modules.finitePresentation_projective_sections N hU
  let F := SheafOfModules.evaluation Z.ringCatSheaf (Opposite.op U)
  have : F.Additive := by
    dsimp [F, SheafOfModules.evaluation]
    infer_instance
  let s := t.map F
  let e : Γ(N, U) ≃ₗ[Γ(Z, U)] Γ(M, U) × Γ(cokernel f, U) :=
    (s.isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
  let q : Γ(N, U) →ₗ[Γ(Z, U)] Γ(cokernel f, U) := ((T.map F).g).hom
  let j : Γ(cokernel f, U) →ₗ[Γ(Z, U)] Γ(N, U) := s.s.hom
  have hsplit : q.comp j = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom s.s_g
    change q.comp j = LinearMap.id at h
    exact h
  have hQfin : Module.Finite Γ(Z, U) Γ(cokernel f, U) :=
    Module.Finite.of_surjective q (by
      intro y
      exact ⟨j y, DFunLike.congr_fun hsplit y⟩)
  have hQproj : Module.Projective Γ(Z, U) Γ(cokernel f, U) :=
    Module.Projective.of_split j q hsplit
  have hQfp := Module.finitePresentation_of_projective Γ(Z, U) Γ(cokernel f, U)
  have hQflat : Module.Flat Γ(Z, U) Γ(cokernel f, U) := inferInstance
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M b
  obtain ⟨hMfp, hMproj⟩ := Scheme.Modules.finitePresentation_projective_sections M hU
  refine ⟨hQfp, hQflat, ?_⟩
  intro p
  have hr := congrFun (Module.rankAtStalk_eq_of_equiv e) p
  have hsum := congrFun (Module.rankAtStalk_prod (R := Γ(Z, U)) Γ(M, U)
    Γ(cokernel f, U)) p
  have hM := Scheme.Modules.rankAtStalk_sections_eq M (r := b) hU p
  have hN := Scheme.Modules.rankAtStalk_sections_eq N (r := k) hU p
  change Module.rankAtStalk Γ(N, U) p =
    Module.rankAtStalk (Γ(M, U) × Γ(cokernel f, U)) p at hr
  rw [hN, hsum, Pi.add_apply, hM] at hr
  omega


private theorem kernel_rank_of_split_epi {X : Scheme.{u}} {M N : X.Modules}
    (q : M ⟶ N) (m b : ℕ) [M.IsFiniteLocallyFreeOfRank m]
    [N.IsFiniteLocallyFreeOfRank b] [IsSplitEpi q] :
    (kernel q).IsFiniteLocallyFreeOfRank (m - b) := by
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree M m
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree N b
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M m
  have := Scheme.Modules.isQuasicoherent_kernel q
  let K := ShortComplex.kernelSequence q
  let t := ShortComplex.Splitting.ofExactOfSection K
    (ShortComplex.kernelSequence_exact q) (section_ q) (IsSplitEpi.id q)
    (by dsimp [K, ShortComplex.kernelSequence]; infer_instance)
  apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_isAffineOpen
  intro U hU
  obtain ⟨hfp, hproj⟩ := Scheme.Modules.finitePresentation_projective_sections M hU
  let E := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)
  have : E.Additive := by dsimp [E, SheafOfModules.evaluation]; infer_instance
  let s := t.map E
  let e : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(kernel q, U) × Γ(N, U) :=
    (s.isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
  let j : Γ(kernel q, U) →ₗ[Γ(X, U)] Γ(M, U) := ((K.map E).f).hom
  let r : Γ(M, U) →ₗ[Γ(X, U)] Γ(kernel q, U) := s.r.hom
  have hsplit : r.comp j = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom s.f_r
    change r.comp j = LinearMap.id at h
    exact h
  have : Module.Finite Γ(X, U) Γ(kernel q, U) :=
    Module.Finite.of_surjective r (fun y ↦ ⟨j y, DFunLike.congr_fun hsplit y⟩)
  have : Module.Projective Γ(X, U) Γ(kernel q, U) :=
    Module.Projective.of_split j r hsplit
  have hKfp := Module.finitePresentation_of_projective Γ(X, U) Γ(kernel q, U)
  have hKflat : Module.Flat Γ(X, U) Γ(kernel q, U) := inferInstance
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N b
  obtain ⟨hNfp, hNproj⟩ := Scheme.Modules.finitePresentation_projective_sections N hU
  refine ⟨hKfp, hKflat, ?_⟩
  intro p
  have hr := congrFun (Module.rankAtStalk_eq_of_equiv e) p
  have hsum := congrFun (Module.rankAtStalk_prod (R := Γ(X, U)) Γ(kernel q, U) Γ(N, U)) p
  have hM := Scheme.Modules.rankAtStalk_sections_eq M (r := m) hU p
  have hN := Scheme.Modules.rankAtStalk_sections_eq N (r := b) hU p
  change Module.rankAtStalk Γ(M, U) p =
    Module.rankAtStalk (Γ(kernel q, U) × Γ(N, U)) p at hr
  rw [hM, hsum, Pi.add_apply, hN] at hr
  omega

/-- The rank needed for the recursive call.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: the quotient `q*F → L` is epi onto an invertible module, hence locally split.
On an open where it is split and on an affine open inside it, the sections of `q*F`
are the product of the kernel sections and the line sections; the kernel sections are
a retract of a finite projective module, hence finitely presented and flat, and their
rank at every prime is `(n+1) - 1 = n` by additivity of `rankAtStalk`. The affine
criterion gives rank `n` on each such open, and these opens cover. -/
theorem completeFlagKernel_rank (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    (completeFlagKernel T n F).IsFiniteLocallyFreeOfRank n := by
  classical
  let D := completeFlagProjectivization T n F
  have : D.L.IsInvertible := realization_line_invertible D
  have : Epi D.quotient := realization_quotient_epi D
  have : ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F).IsFiniteLocallyFreeOfRank
      (n + 1) := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
        ((projectiveBundleTensorPullbackIso D.A.data.relProjHom).app F).symm
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible D.L
  have : D.L.IsFiniteLocallyFreeOfRank 1 :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one D.L).mp inferInstance
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree D.L 1
  choose U hx s hs using Scheme.Modules.exists_local_section_of_epi D.quotient
  change (kernel D.quotient).IsFiniteLocallyFreeOfRank n
  apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top _ U
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩)
  intro x
  let R := Scheme.Modules.restrictFunctor (U x).ι
  have : IsSplitEpi (R.map D.quotient) := IsSplitEpi.mk' ⟨s x, hs x⟩
  have : (R.obj ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F)
      ).IsFiniteLocallyFreeOfRank (n + 1) := inferInstance
  have : (R.obj D.L).IsFiniteLocallyFreeOfRank 1 := inferInstance
  have hker : (kernel (R.map D.quotient)).IsFiniteLocallyFreeOfRank n := by
    simpa only [Nat.add_sub_cancel] using kernel_rank_of_split_epi (R.map D.quotient) (n + 1) 1
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (PreservesKernel.iso R D.quotient).symm

/-- A scheme over `T` together with a family of actual subsheaf presentations.
Levels past the rank are repeated final levels; only levels `0,…,r` are used.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
structure CompleteFlagBundleData (T : Scheme.{u}) (F : T.Modules) where
  scheme : Scheme.{u}
  projection : scheme ⟶ T
  level : ℕ → scheme.Modules
  inclusion : ∀ i : ℕ, level i ⟶ (Scheme.Modules.tensorPullback projection).obj F

/-- The identity bundle with its zero and full levels, used at ranks zero and one.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagIdentity (T : Scheme.{u}) (F : T.Modules) :
    CompleteFlagBundleData T F where
  scheme := T
  projection := 𝟙 T
  level i := if i = 0 then 0 else (Scheme.Modules.tensorPullback (𝟙 T)).obj F
  inclusion i := if h : i = 0 then
    eqToHom (if_pos h) ≫ 0
    else eqToHom (if_neg h) ≫ 𝟙 _

/-- Extend a recursive kernel filtration by its ambient pulled-back module.
The embeddings use the actual kernel inclusion and the section-normalized comparison
`h* q* F ≅ (h ≫ q)* F`. No global splitting is chosen.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagExtend {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F)
    (G : CompleteFlagBundleData D.A.data.relProj (kernel D.quotient)) (r : ℕ) :
    CompleteFlagBundleData T F where
  scheme := G.scheme
  projection := G.projection ≫ D.A.data.relProjHom
  level i := if i < r then G.level i else
    (Scheme.Modules.tensorPullback (G.projection ≫ D.A.data.relProjHom)).obj F
  inclusion i := if h : i < r then
    eqToHom (if_pos h) ≫ G.inclusion i ≫
      (Scheme.Modules.tensorPullback G.projection).map (kernel.ι D.quotient) ≫
      ((Scheme.Modules.tensorPullbackSectionComp G.projection D.A.data.relProjHom).app F).inv
    else eqToHom (if_neg h) ≫ 𝟙 _

/-- The complete flag bundle, recursively projectivizing the tautological kernel.
At ranks zero and one its projection is the identity. At rank `n+2` it is the
composite of the recursively constructed rank-`n+1` flag projection with the
projectivization projection; its earlier levels are the recursive kernel levels.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagBundle : (r : ℕ) → (T : Scheme.{u}) → (F : T.Modules) →
    [F.IsFiniteLocallyFreeOfRank r] → CompleteFlagBundleData T F
  | 0, T, F, _ => completeFlagIdentity T F
  | 1, T, F, _ => completeFlagIdentity T F
  | n + 2, T, F, _ =>
    let D := completeFlagProjectivization T (n + 1) F
    letI := completeFlagKernel_rank T (n + 1) F
    completeFlagExtend D
      (completeFlagBundle (n + 1) D.A.data.relProj (completeFlagKernel T (n + 1) F))
      (n + 2)
termination_by structural r => r

/-- The recursive kernel flag, exposing the map `h` used at rank `n+2`.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagPredecessor (T : Scheme.{u}) (n : ℕ) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank (n + 2)] :
    CompleteFlagBundleData (completeFlagProjectivization T (n + 1) F).A.data.relProj
      (completeFlagKernel T (n + 1) F) :=
  letI := completeFlagKernel_rank T (n + 1) F
  completeFlagBundle (n + 1) _ (completeFlagKernel T (n + 1) F)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible]
  projectiveBundleTensorPullbackIso Scheme.Modules.tensorPullbackSectionComp
  Scheme.Modules.tensorPullbackSectionId

private theorem split_epi_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (f : A ⟶ B) [IsSplitEpi (F.map f)] :
    IsSplitEpi (G.map f) := by
  apply IsSplitEpi.mk'
  refine ⟨e.inv.app B ≫ section_ (F.map f) ≫ e.hom.app A, ?_⟩
  rw [Category.assoc, Category.assoc, ← e.hom.naturality, ← Category.assoc (section_ (F.map f)),
    IsSplitEpi.id, Category.id_comp, e.inv_hom_id_app]

private theorem kernel_split {C : Type*} [Category C] [Preadditive C]
    {A B : C} (f : A ⟶ B) [HasKernel f] [IsSplitEpi f] :
    IsSplitMono (kernel.ι f) := by
  let r := kernel.lift f (𝟙 A - f ≫ section_ f) (by simp)
  apply IsSplitMono.mk'
  refine ⟨r, ?_⟩
  apply (cancel_mono (kernel.ι f)).mp
  simp [r, Preadditive.comp_sub]

private theorem map_kernel_split {C D : Type*} [Category C] [Preadditive C]
    [Category D] [Preadditive D] (H : C ⥤ D) [H.Additive]
    {A B : C} (f : A ⟶ B) [HasKernel f] [HasKernel (H.map f)]
    [PreservesLimit (parallelPair f 0) H] [IsSplitEpi (H.map f)] :
    IsSplitMono (H.map (kernel.ι f)) := by
  have := kernel_split (H.map f)
  have : IsSplitMono ((PreservesKernel.iso H f).hom ≫ kernel.ι (H.map f)) :=
    inferInstance
  simpa using this

private theorem restrict_limits {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  let R := Scheme.Modules.restrictFunctor f
  let Z := Scheme.Modules.toPresheaf X
  let Z' := Scheme.Modules.toPresheaf Y
  let eR : R ⋙ Z ≅ Z' ⋙ (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op :=
    Iso.refl _
  have : PreservesFiniteLimits Z' := by dsimp only [Z']; infer_instance
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ Ab).obj f.opensFunctor.op) := by infer_instance
  have : PreservesFiniteLimits (R ⋙ Z) := preservesFiniteLimits_of_natIso eR.symm
  exact preservesFiniteLimits_of_reflects_of_preserves R Z

private theorem restrict_kernel_split {X : Scheme.{u}} {A B : X.Modules}
    (f : A ⟶ B) (U : X.Opens)
    [IsSplitEpi ((Scheme.Modules.tensorPullback U.ι).map f)] :
    IsSplitMono ((Scheme.Modules.restrictFunctor U.ι).map (kernel.ι f)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let a : Scheme.Modules.tensorPullback U.ι ≅ R :=
    projectiveBundleTensorPullbackIso U.ι ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  have : IsSplitEpi (R.map f) := split_epi_iso a f
  have : PreservesFiniteLimits R := restrict_limits U.ι
  have : R.Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  exact map_kernel_split R f

private theorem tautological_locally_split_kernel (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    ∀ x : (completeFlagProjectivization T n F).A.data.relProj,
      ∃ U : (completeFlagProjectivization T n F).A.data.relProj.Opens, x ∈ U ∧
        IsSplitMono ((Scheme.Modules.restrictFunctor U.ι).map
          (kernel.ι (completeFlagProjectivization T n F).quotient)) := by
  intro x
  let D := completeFlagProjectivization T n F
  obtain ⟨U, hx, s, hs⟩ := completeFlagKernel_pullback_locally_split T n F
    D.A.data.relProj (𝟙 _) x
  let H := Scheme.Modules.tensorPullback U.ι
  let e := Functor.isoWhiskerRight (Scheme.Modules.tensorPullbackSectionId D.A.data.relProj) H
  have : IsSplitEpi ((Scheme.Modules.tensorPullback (𝟙 D.A.data.relProj) ⋙ H).map
      D.quotient) := IsSplitEpi.mk' ⟨s, hs⟩
  have : IsSplitEpi (H.map D.quotient) := split_epi_iso e D.quotient
  exact ⟨U, hx, restrict_kernel_split D.quotient U⟩

private theorem pullback_mono_of_local_retractions {X Y : Scheme.{u}}
    {A B : X.Modules} (f : A ⟶ B)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsSplitMono ((Scheme.Modules.restrictFunctor U.ι).map f)) (g : Y ⟶ X) :
    Mono ((Scheme.Modules.tensorPullback g).map f) := by
  classical
  choose U hx hs using h
  let V (y : Y) := g ⁻¹ᵁ U (g y)
  have hm : Mono ((Scheme.Modules.pullback g).map f) := by
    apply Scheme.Modules.mono_of_restrict _ V
    · exact eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hx (g y)⟩
    · intro y
      let R := Scheme.Modules.restrictFunctor (U (g y)).ι
      let G := Scheme.Modules.pullback (g ∣_ U (g y))
      let H := Scheme.Modules.restrictFunctor (V y).ι
      let e : Scheme.Modules.pullback g ⋙ H ≅ R ⋙ G :=
        Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback (V y).ι) ≪≫
          Scheme.Modules.pullbackComp (V y).ι g ≪≫
          Scheme.Modules.pullbackCongr (morphismRestrict_ι g (U (g y))).symm ≪≫
          (Scheme.Modules.pullbackComp (g ∣_ U (g y)) (U (g y)).ι).symm ≪≫
          Functor.isoWhiskerRight
            (Scheme.Modules.restrictFunctorIsoPullback (U (g y)).ι).symm G
      have : IsSplitMono (R.map f) := hs (g y)
      have hj : G.map (R.map f) ≫
          G.map (retraction (R.map f)) = 𝟙 _ := by
        rw [← G.map_comp, IsSplitMono.id, G.map_id]
      have : IsSplitMono (H.map ((Scheme.Modules.pullback g).map
          f)) := IsSplitMono.mk'
        { retraction := e.hom.app _ ≫ G.map (retraction (R.map f)) ≫
            e.inv.app _
          id := by
            change (Scheme.Modules.pullback g ⋙ H).map f ≫ _ = _
            rw [← Category.assoc, e.hom.naturality, Functor.comp_map, Category.assoc,
              ← Category.assoc (G.map (R.map f)), hj, Category.id_comp]
            exact e.hom_inv_id_app _ }
      infer_instance
  let e := projectiveBundleTensorPullbackIso g
  have he : (Scheme.Modules.tensorPullback g).map f =
      e.hom.app _ ≫ (Scheme.Modules.pullback g).map f ≫ e.inv.app _ := by
    rw [← e.hom.naturality_assoc, e.hom_inv_id_app, Category.comp_id]
  rw [he]
  infer_instance

private theorem tautological_kernel_pullback_mono (T : Scheme.{u}) (n : ℕ)
    (F : T.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)]
    (Y : Scheme.{u}) (g : Y ⟶ (completeFlagProjectivization T n F).A.data.relProj) :
    Mono ((Scheme.Modules.tensorPullback g).map
      (kernel.ι (completeFlagProjectivization T n F).quotient)) := by
  exact pullback_mono_of_local_retractions _ (tautological_locally_split_kernel T n F) g

private theorem identity_mono {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (A : C) (i : ℕ) :
    Mono (if h : i = 0 then (eqToHom (if_pos h) :
      (if i = 0 then 0 else A) ⟶ 0) ≫ (0 : 0 ⟶ A)
      else eqToHom (if_neg h) ≫ 𝟙 A) := by
  split <;> infer_instance

private theorem extend_mono {C : Type*} [Category C] {K A : C}
    (L : ℕ → C) (j : ∀ i, L i ⟶ K) (k : K ⟶ A) [∀ i, Mono (j i)] [Mono k]
    (r i : ℕ) :
    Mono (if h : i < r then (eqToHom (if_pos h) :
      (if i < r then L i else A) ⟶ L i) ≫ j i ≫ k
      else eqToHom (if_neg h) ≫ 𝟙 A) := by
  split <;> infer_instance

private theorem identity_mono_data (T : Scheme.{u}) (F : T.Modules) (i : ℕ) :
    Mono ((completeFlagIdentity T F).inclusion i) :=
  identity_mono ((Scheme.Modules.tensorPullback (𝟙 T)).obj F) i

private theorem extend_mono_data {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F)
    (G : CompleteFlagBundleData D.A.data.relProj (kernel D.quotient))
    [∀ i, Mono (G.inclusion i)]
    [Mono ((Scheme.Modules.tensorPullback G.projection).map (kernel.ι D.quotient))]
    (r i : ℕ) : Mono ((completeFlagExtend D G r).inclusion i) :=
  extend_mono G.level G.inclusion
    ((Scheme.Modules.tensorPullback G.projection).map (kernel.ι D.quotient) ≫
      ((Scheme.Modules.tensorPullbackSectionComp G.projection D.A.data.relProjHom).app F).inv) r i

attribute [local irreducible] completeFlagBundle completeFlagIdentity completeFlagExtend

/-- Each presented level is a subsheaf.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: for the identity cases, the zero and identity maps are monomorphisms.
In the induction step the recursive maps are monic by induction. The chart
splitting `τⱼ ↦ vⱼ` makes the kernel inclusion split on the standard open cover;
a split inclusion remains split after any pullback. Composing this pulled-back
inclusion with the recursive inclusion and the pullback comparison remains monic. -/
theorem completeFlagBundle_mono (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) :
    Mono ((completeFlagBundle r T F).inclusion i) := by
  induction r using Nat.strong_induction_on generalizing T F i with
  | h r ih =>
    cases r with
    | zero =>
      rw [completeFlagBundle]
      exact identity_mono_data T F i
    | succ r =>
      cases r with
      | zero =>
        rw [completeFlagBundle]
        exact identity_mono_data T F i
      | succ n =>
        rw [completeFlagBundle]
        let D := completeFlagProjectivization T (n + 1) F
        let := completeFlagKernel_rank T (n + 1) F
        let G := completeFlagBundle (n + 1) D.A.data.relProj
          (completeFlagKernel T (n + 1) F)
        have hm : ∀ k, Mono (G.inclusion k) := fun k ↦
          ih (n + 1) (by omega) D.A.data.relProj (completeFlagKernel T (n + 1) F) k
        have hk : Mono ((Scheme.Modules.tensorPullback G.projection).map (kernel.ι D.quotient)) :=
          tautological_kernel_pullback_mono T (n + 1) F G.scheme G.projection
        exact @extend_mono_data T F D G hm hk (n + 2) i

private theorem flag_identity_steps {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] (A : C) (i : ℕ) :
    ∃ f : (if i = 0 then 0 else A) ⟶ (if i + 1 = 0 then 0 else A),
      f ≫ (if h : i + 1 = 0 then eqToHom (if_pos h) ≫ 0
        else eqToHom (if_neg h) ≫ 𝟙 A) =
      (if h : i = 0 then eqToHom (if_pos h) ≫ 0
        else eqToHom (if_neg h) ≫ 𝟙 A) := by
  have hi : i + 1 ≠ 0 := by omega
  refine ⟨(if h : i = 0 then eqToHom (if_pos h) ≫ 0
    else eqToHom (if_neg h) ≫ 𝟙 A) ≫ eqToHom (if_neg hi).symm, ?_⟩
  simp only [dif_neg hi, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem flag_extend_steps {C : Type*} [Category C] {K A : C}
    (L : ℕ → C) (j : ∀ i, L i ⟶ K) (k : K ⟶ A) (r i : ℕ)
    (h : ∃ f : L i ⟶ L (i + 1), f ≫ j (i + 1) = j i) :
    ∃ f : (if i < r then L i else A) ⟶ (if i + 1 < r then L (i + 1) else A),
      f ≫ (if h : i + 1 < r then eqToHom (if_pos h) ≫ j (i + 1) ≫ k
        else eqToHom (if_neg h) ≫ 𝟙 A) =
      (if h : i < r then eqToHom (if_pos h) ≫ j i ≫ k
        else eqToHom (if_neg h) ≫ 𝟙 A) := by
  by_cases hi : i + 1 < r
  · have hi' : i < r := by omega
    obtain ⟨f, hf⟩ := h
    refine ⟨eqToHom (if_pos hi') ≫ f ≫ eqToHom (if_pos hi).symm, ?_⟩
    simp only [dif_pos hi, dif_pos hi', Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [← Category.assoc f, hf]
  · by_cases hi' : i < r
    · refine ⟨eqToHom (if_pos hi') ≫ j i ≫ k ≫ eqToHom (if_neg hi).symm, ?_⟩
      simp only [dif_neg hi, dif_pos hi', Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.comp_id]
    · refine ⟨eqToHom (if_neg hi') ≫ eqToHom (if_neg hi).symm, ?_⟩
      simp only [dif_neg hi, dif_neg hi', eqToHom_trans, Category.comp_id]

attribute [local semireducible] completeFlagIdentity completeFlagExtend

private theorem identity_steps_data (T : Scheme.{u}) (F : T.Modules) (i : ℕ) :
    ∃ f : (completeFlagIdentity T F).level i ⟶ (completeFlagIdentity T F).level (i + 1),
      f ≫ (completeFlagIdentity T F).inclusion (i + 1) =
        (completeFlagIdentity T F).inclusion i :=
  flag_identity_steps ((Scheme.Modules.tensorPullback (𝟙 T)).obj F) i

private theorem extend_steps_data {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F)
    (G : CompleteFlagBundleData D.A.data.relProj (kernel D.quotient)) (r i : ℕ)
    (h : ∃ f : G.level i ⟶ G.level (i + 1), f ≫ G.inclusion (i + 1) = G.inclusion i) :
    ∃ f : (completeFlagExtend D G r).level i ⟶ (completeFlagExtend D G r).level (i + 1),
      f ≫ (completeFlagExtend D G r).inclusion (i + 1) =
        (completeFlagExtend D G r).inclusion i :=
  flag_extend_steps G.level G.inclusion
    ((Scheme.Modules.tensorPullback G.projection).map (kernel.ι D.quotient) ≫
      ((Scheme.Modules.tensorPullbackSectionComp G.projection D.A.data.relProjHom).app F).inv)
    r i h

attribute [local irreducible] projectiveBundlePullbackAdjunction
  completeFlagIdentity completeFlagExtend
/-- The levels form an increasing filtration; the factor map is uniquely determined.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: at ranks zero and one the factors are zero or identity maps. At a higher
rank use the recursive factor while both levels are kernel levels. At the last
step use the pulled-back kernel inclusion, composed with the last recursive
level map. Thereafter use identities. The equations follow by composition with
the ambient inclusion. Uniqueness follows from `completeFlagBundle_mono`. -/
theorem completeFlagBundle_step_unique (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) :
    ∃! f : (completeFlagBundle r T F).level i ⟶ (completeFlagBundle r T F).level (i + 1),
      f ≫ (completeFlagBundle r T F).inclusion (i + 1) =
        (completeFlagBundle r T F).inclusion i := by
  classical
  have hex : ∃ f : (completeFlagBundle r T F).level i ⟶
      (completeFlagBundle r T F).level (i + 1),
      f ≫ (completeFlagBundle r T F).inclusion (i + 1) =
        (completeFlagBundle r T F).inclusion i := by
    induction r using Nat.strong_induction_on generalizing T F with
    | h r ih =>
      cases r with
      | zero =>
        rw [completeFlagBundle]
        exact identity_steps_data T F i
      | succ r =>
        cases r with
        | zero =>
          rw [completeFlagBundle]
          exact identity_steps_data T F i
        | succ n =>
          rw [completeFlagBundle]
          let D := completeFlagProjectivization T (n + 1) F
          let := completeFlagKernel_rank T (n + 1) F
          let G := completeFlagBundle (n + 1) D.A.data.relProj
            (completeFlagKernel T (n + 1) F)
          exact extend_steps_data D G (n + 2) i
            (ih (n + 1) (by omega) D.A.data.relProj (completeFlagKernel T (n + 1) F))
  obtain ⟨f, hf⟩ := hex
  let := completeFlagBundle_mono r T F (i + 1)
  exact ⟨f, hf, fun g hg ↦ (cancel_mono
    ((completeFlagBundle r T F).inclusion (i + 1))).mp (hg.trans hf.symm)⟩

attribute [local semireducible] completeFlagBundle completeFlagIdentity completeFlagExtend

/-- The uniquely characterized inclusion `Fᵢ ⟶ Fᵢ₊₁`.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagStep (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) :
    (completeFlagBundle r T F).level i ⟶ (completeFlagBundle r T F).level (i + 1) :=
  Classical.choose (completeFlagBundle_step_unique r T F i)

attribute [local irreducible] completeFlagStep

/-- The successive quotient `Qᵢ₊₁ = Fᵢ₊₁/Fᵢ`, taken in sheaves of modules.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle). -/
noncomputable def completeFlagQuotient (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (i : ℕ) : (completeFlagBundle r T F).scheme.Modules :=
  cokernel (completeFlagStep r T F i)

set_option backward.isDefEq.respectTransparency false

private theorem identity_top_iso (T : Scheme.{u}) (F : T.Modules) (r : ℕ)
    (hr : r ≠ 0) : IsIso ((completeFlagIdentity T F).inclusion r) := by
  dsimp only [completeFlagIdentity]
  simp only [dif_neg hr]
  infer_instance

private theorem extend_top_iso {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F)
    (G : CompleteFlagBundleData D.A.data.relProj (kernel D.quotient)) (r : ℕ) :
    IsIso ((completeFlagExtend D G r).inclusion r) := by
  dsimp only [completeFlagExtend]
  simp only [dif_neg (Nat.lt_irrefl r)]
  infer_instance

private theorem flag_top_iso (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (hr : r ≠ 0) :
    IsIso ((completeFlagBundle r T F).inclusion r) := by
  cases r with
  | zero => exact (hr rfl).elim
  | succ r =>
    cases r with
    | zero =>
      rw [completeFlagBundle]
      exact identity_top_iso T F 1 (by omega)
    | succ n =>
      rw [completeFlagBundle]
      exact extend_top_iso _ _ _

private theorem cokernel_iso_of_kernel_square {C D : Type*}
    [Category C] [Abelian C] [Category D] [Abelian D]
    (H : C ⥤ D) [H.Additive] [PreservesColimits H]
    {A B : C} (q : A ⟶ B) [Epi q] {X Y : D} (f : X ⟶ Y)
    (eX : X ≅ H.obj (kernel q)) (eY : Y ≅ H.obj A)
    (hw : f ≫ eY.hom = eX.hom ≫ H.map (kernel.ι q)) :
    ∃ θ : cokernel f ≅ H.obj B,
      cokernel.π f ≫ θ.hom = eY.hom ≫ H.map q := by
  let c := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel q)
  let hc := isColimitCoforkMapOfIsColimit' H (kernel.condition q) c
  let e : cokernel (H.map (kernel.ι q)) ≅ H.obj B :=
    (cokernelIsCokernel (H.map (kernel.ι q))).coconePointUniqueUpToIso hc
  have he : cokernel.π (H.map (kernel.ι q)) ≫ e.hom = H.map q := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (H.map (kernel.ι q))) hc WalkingParallelPair.one
  refine ⟨cokernel.mapIso f (H.map (kernel.ι q)) eX eY hw ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, cokernel.mapIso_hom, cokernel.map,
    cokernel.π_desc_assoc, Category.assoc, he]

/-- The last quotient is the pullback of the tautological line by the recursive map,
with quotient map the pulled-back tautological quotient `h*ε` under `p*F ≅ h*q*F`.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: the top inclusions of the recursive and of the extended filtration are
isomorphisms, and the penultimate step of the extended filtration is, through them and
the pullback-composition isomorphism, the pulled-back kernel inclusion `h*K → h*q*F`.
The quotient is epi, so it is the cokernel of its kernel; `h*` is a left adjoint and
preserves this cokernel. The cokernel universal property gives the isomorphism to
`h*L` and its quotient-map equation. -/
theorem completeFlagBundle_last_quotient (T : Scheme.{u}) (n : ℕ) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank (n + 2)] :
    ∃ θ : completeFlagQuotient (n + 2) T F (n + 1) ≅
        (Scheme.Modules.tensorPullback (completeFlagPredecessor T n F).projection).obj
          (completeFlagProjectivization T (n + 1) F).L,
      cokernel.π (completeFlagStep (n + 2) T F (n + 1)) ≫ θ.hom =
        (completeFlagBundle (n + 2) T F).inclusion (n + 2) ≫
          ((Scheme.Modules.tensorPullbackSectionComp (completeFlagPredecessor T n F).projection
            (completeFlagProjectivization T (n + 1) F).A.data.relProjHom).app F).hom ≫
          (Scheme.Modules.tensorPullback (completeFlagPredecessor T n F).projection).map
            (completeFlagProjectivization T (n + 1) F).quotient := by
  classical
  let D := completeFlagProjectivization T (n + 1) F
  let G := completeFlagPredecessor T n F
  let H := Scheme.Modules.tensorPullback G.projection
  let : H.IsLeftAdjoint :=
    (Scheme.Modules.tensorPullbackSectionAdjunction G.projection).isLeftAdjoint
  have : H.Additive :=
    Functor.additive_of_iso (projectiveBundleTensorPullbackIso G.projection).symm
  have : Epi D.quotient := realization_quotient_epi D
  have : IsIso (G.inclusion (n + 1)) := by
    let := completeFlagKernel_rank T (n + 1) F
    exact flag_top_iso (n + 1) _ (completeFlagKernel T (n + 1) F) (by omega)
  have : IsIso ((completeFlagBundle (n + 2) T F).inclusion (n + 2)) :=
    flag_top_iso _ _ _ (by omega)
  let eX : (completeFlagBundle (n + 2) T F).level (n + 1) ≅
      H.obj (kernel D.quotient) :=
    eqToIso (by simp only [completeFlagBundle, completeFlagExtend,
      show n + 1 < n + 2 by omega, if_pos]; rfl) ≪≫ asIso (G.inclusion (n + 1))
  let eY := asIso ((completeFlagBundle (n + 2) T F).inclusion (n + 2)) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp G.projection D.A.data.relProjHom).app F
  have hw : completeFlagStep (n + 2) T F (n + 1) ≫ eY.hom =
      eX.hom ≫ H.map (kernel.ι D.quotient) := by
    have hs : completeFlagStep (n + 2) T F (n + 1) ≫
        (completeFlagBundle (n + 2) T F).inclusion (n + 2) =
          (completeFlagBundle (n + 2) T F).inclusion (n + 1) := by
      simpa only [completeFlagStep, Nat.add_assoc] using
        (Classical.choose_spec (completeFlagBundle_step_unique (n + 2) T F (n + 1))).1
    dsimp only [eY, Iso.trans_hom, asIso_hom]
    rw [← Category.assoc, hs]
    simp only [completeFlagBundle, completeFlagExtend,
      show n + 1 < n + 2 by omega, dif_pos, Category.assoc]
    dsimp only [eX, G, D, H, completeFlagPredecessor,
      Iso.trans_hom, eqToIso.hom, asIso_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact cokernel_iso_of_kernel_square H D.quotient _ eX eY hw

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] completeFlagBundle completeFlagQuotient
  completeFlagPredecessor completeFlagKernel completeFlagExtend completeFlagIdentity

attribute [local semireducible] completeFlagIdentity completeFlagExtend completeFlagKernel
  completeFlagStep completeFlagQuotient

private theorem split_mono_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (f : A ⟶ B) [IsSplitMono (F.map f)] :
    IsSplitMono (G.map f) := by
  apply IsSplitMono.mk'
  refine ⟨e.inv.app B ≫ retraction (F.map f) ≫ e.hom.app A, ?_⟩
  rw [← Category.assoc, e.inv.naturality, Category.assoc,
    ← Category.assoc (F.map f), IsSplitMono.id, Category.id_comp, e.inv_hom_id_app]

private def flagLocallySplit {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    IsSplitMono ((Scheme.Modules.restrictFunctor U.ι).map f)

private theorem flag_locally_split_of_split {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [IsSplitMono f] : flagLocallySplit f := by
  intro x
  exact ⟨⊤, trivial, inferInstance⟩

private theorem restrict_split_smaller {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {U V : X.Opens} (h : U ≤ V)
    [IsSplitMono ((Scheme.Modules.restrictFunctor V.ι).map f)] :
    IsSplitMono ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  let G := Scheme.Modules.restrictFunctor (X.homOfLE h)
  let e := Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm ≪≫
    Scheme.Modules.restrictFunctorComp (X.homOfLE h) V.ι
  have : IsSplitMono ((Scheme.Modules.restrictFunctor V.ι ⋙ G).map f) := by
    change IsSplitMono (G.map ((Scheme.Modules.restrictFunctor V.ι).map f))
    infer_instance
  exact split_mono_iso e.symm f

private theorem flag_locally_split_comp {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (hf : flagLocallySplit f) (hg : flagLocallySplit g) :
    flagLocallySplit (f ≫ g) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hf x
  obtain ⟨V, hxV, hV⟩ := hg x
  have := restrict_split_smaller f (inf_le_left : U ⊓ V ≤ U)
  have := restrict_split_smaller g (inf_le_right : U ⊓ V ≤ V)
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ?_⟩
  rw [Functor.map_comp]
  infer_instance

private theorem flag_locally_split_pullback {X Y : Scheme.{u}}
    {A B : X.Modules} (f : A ⟶ B) (h : flagLocallySplit f) (g : Y ⟶ X) :
    flagLocallySplit ((Scheme.Modules.tensorPullback g).map f) := by
  intro y
  obtain ⟨U, hx, hs⟩ := h (g y)
  let V := g ⁻¹ᵁ U
  let R := Scheme.Modules.restrictFunctor U.ι
  let G := Scheme.Modules.pullback (g ∣_ U)
  let H := Scheme.Modules.restrictFunctor V.ι
  let e : Scheme.Modules.tensorPullback g ⋙ H ≅ R ⋙ G :=
    Functor.isoWhiskerRight (projectiveBundleTensorPullbackIso g) H ≪≫
      Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback V.ι) ≪≫
      Scheme.Modules.pullbackComp V.ι g ≪≫
      Scheme.Modules.pullbackCongr (morphismRestrict_ι g U).symm ≪≫
      (Scheme.Modules.pullbackComp (g ∣_ U) U.ι).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm G
  have : IsSplitMono ((R ⋙ G).map f) := by
    have : IsSplitMono (R.map f) := hs
    change IsSplitMono (G.map (R.map f))
    infer_instance
  exact ⟨V, hx, split_mono_iso e.symm f⟩

private theorem flag_free_zero {X : Scheme.{u}} :
    IsZero (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 0))) :=
  (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun i ↦ isEmptyElim i)

private theorem flag_zero_rank (X : Scheme.{u}) :
    (0 : X.Modules).IsFiniteLocallyFreeOfRank 0 :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (r := 0)
    (flag_free_zero (X := X)).isoZero

private theorem flag_rank_zero_isZero {X : Scheme.{u}} (M : X.Modules)
    [M.IsFiniteLocallyFreeOfRank 0] : IsZero M := by
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := 0)
  exact Scheme.Modules.isZero_of_iSup_eq_top M U hU
    (fun i ↦ flag_free_zero.of_iso (e i).some)

private theorem flag_identity_level_rank (T : Scheme.{u}) (F : T.Modules)
    (r i : ℕ) [F.IsFiniteLocallyFreeOfRank r] (hr : r ≤ 1) (hi : i ≤ r) :
    ((completeFlagIdentity T F).level i).IsFiniteLocallyFreeOfRank i := by
  by_cases h : i = 0
  · subst i
    change (0 : T.Modules).IsFiniteLocallyFreeOfRank 0
    exact flag_zero_rank T
  · have hir : i = r := by omega
    subst i
    have hF : ((Scheme.Modules.tensorPullback (𝟙 T)).obj F).IsFiniteLocallyFreeOfRank r :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
        ((projectiveBundleTensorPullbackIso _).app F).symm
    change (if r = 0 then (0 : T.Modules) else
      (Scheme.Modules.tensorPullback (𝟙 T)).obj F).IsFiniteLocallyFreeOfRank r
    rw [if_neg h]
    exact hF

private theorem flag_identity_split (T : Scheme.{u}) (F : T.Modules) (i : ℕ) :
    flagLocallySplit ((completeFlagIdentity T F).inclusion i) := by
  have : IsSplitMono ((completeFlagIdentity T F).inclusion i) := by
    by_cases h : i = 0
    · subst i
      have hz : IsZero ((completeFlagIdentity T F).level 0) := by
        change IsZero (0 : T.Modules)
        exact isZero_zero T.Modules
      exact IsSplitMono.mk' ⟨hz.from_ _, hz.eq_of_src _ _⟩
    · have := identity_top_iso T F i h
      infer_instance
  exact flag_locally_split_of_split _

private theorem flag_extend_split {T : Scheme.{u}} {F : T.Modules}
    (D : ProjectiveBundleRealization T F)
    (G : CompleteFlagBundleData D.A.data.relProj (kernel D.quotient)) (r i : ℕ)
    (hG : flagLocallySplit (G.inclusion i))
    (hK : flagLocallySplit ((Scheme.Modules.tensorPullback G.projection).map
      (kernel.ι D.quotient))) :
    flagLocallySplit ((completeFlagExtend D G r).inclusion i) := by
  dsimp only [completeFlagExtend]
  split
  · apply flag_locally_split_comp _ _ (flag_locally_split_of_split _)
    apply flag_locally_split_comp _ _ hG
    exact flag_locally_split_comp _ _ hK (flag_locally_split_of_split _)
  · exact flag_locally_split_of_split _

private theorem flag_level_induction (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] :
    IsZero ((completeFlagBundle r T F).level 0) ∧
    (∀ i, i ≤ r → ((completeFlagBundle r T F).level i).IsFiniteLocallyFreeOfRank i) ∧
    (∀ i, flagLocallySplit ((completeFlagBundle r T F).inclusion i)) := by
  induction r using Nat.strong_induction_on generalizing T F with
  | h r ih =>
    cases r with
    | zero =>
      rw [completeFlagBundle]
      refine ⟨?_, fun i hi ↦ flag_identity_level_rank T F 0 i (by omega) hi,
        flag_identity_split T F⟩
      change IsZero (0 : T.Modules)
      exact isZero_zero T.Modules
    | succ r =>
      cases r with
      | zero =>
        rw [completeFlagBundle]
        refine ⟨?_, fun i hi ↦ flag_identity_level_rank T F 1 i (by omega) hi,
          flag_identity_split T F⟩
        change IsZero (0 : T.Modules)
        exact isZero_zero T.Modules
      | succ n =>
        let D := completeFlagProjectivization T (n + 1) F
        let := completeFlagKernel_rank T (n + 1) F
        let G := completeFlagBundle (n + 1) D.A.data.relProj
          (completeFlagKernel T (n + 1) F)
        obtain ⟨hzero, hrank, hsplit⟩ := ih (n + 1) (by omega)
          D.A.data.relProj (completeFlagKernel T (n + 1) F)
        rw [completeFlagBundle]
        refine ⟨?_, ?_, ?_⟩
        · change IsZero (if 0 < n + 2 then G.level 0 else
            (Scheme.Modules.tensorPullback (G.projection ≫ D.A.data.relProjHom)).obj F)
          rw [if_pos (by omega)]
          exact hzero
        · intro i hi
          by_cases hir : i < n + 2
          · change (if i < n + 2 then G.level i else
              (Scheme.Modules.tensorPullback (G.projection ≫ D.A.data.relProjHom)).obj F
              ).IsFiniteLocallyFreeOfRank i
            rw [if_pos hir]
            exact hrank i (by omega)
          · have hir' : i = n + 2 := by omega
            subst i
            have hF : ((Scheme.Modules.tensorPullback
                (G.projection ≫ D.A.data.relProjHom)).obj F).IsFiniteLocallyFreeOfRank
                (n + 2) := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
                  ((projectiveBundleTensorPullbackIso _).app F).symm
            change (if n + 2 < n + 2 then G.level (n + 2) else
              (Scheme.Modules.tensorPullback (G.projection ≫ D.A.data.relProjHom)).obj F
              ).IsFiniteLocallyFreeOfRank (n + 2)
            rw [if_neg (Nat.lt_irrefl _)]
            exact hF
        · intro i
          exact flag_extend_split D G (n + 2) i (hsplit i)
            (flag_locally_split_pullback _ (tautological_locally_split_kernel T (n + 1) F)
              G.projection)

private theorem flag_cokernel_rank_of_local_split {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) (k b : ℕ)
    [M.IsFiniteLocallyFreeOfRank b] [N.IsFiniteLocallyFreeOfRank k]
    (h : flagLocallySplit f) : (cokernel f).IsFiniteLocallyFreeOfRank (k - b) := by
  classical
  choose U hx hs using h
  apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top _ U
  · exact eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    let H := Scheme.Modules.restrictFunctor (U x).ι
    have : IsSplitMono (H.map f) := hs x
    have : (H.obj M).IsFiniteLocallyFreeOfRank b := inferInstance
    have : (H.obj N).IsFiniteLocallyFreeOfRank k := inferInstance
    have := flag_cokernel_rank_of_split (H.map f) k b
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (PreservesCokernel.iso H f).symm

/-- Endpoints, line quotients and the vector subbundle property of the universal filtration.
Source: Stacks, Tag 02UL (blueprint: def-pur-complete-flag-bundle).
Proof: induct on the rank, showing simultaneously that level zero is zero, level `i`
is finite locally free of rank `i` for `i ≤ r`, and every inclusion into `p*F` is
locally split. Ranks zero and one use the zero and identity inclusions. At rank `n+2`
the recursive inclusions and the pulled-back tautological kernel inclusion (locally
split by `completeFlagKernel_pullback_locally_split`) compose; the final inclusion is
an isomorphism. Each step is locally split, by a local retraction of the ambient
inclusion. A split inclusion of ranks `b ≤ k` has cokernel of rank `k - b` (affine
product decomposition, finite projective retract, stalk-rank additivity); restriction
preserves cokernels. Hence step quotients have rank one and are invertible, and ambient
quotients are locally free. In rank zero `p*F` is locally zero, hence zero. -/
theorem completeFlagBundle_properties (r : ℕ) (T : Scheme.{u}) (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] :
    IsZero ((completeFlagBundle r T F).level 0) ∧
    IsIso ((completeFlagBundle r T F).inclusion r) ∧
    (∀ i : ℕ, i < r → (completeFlagQuotient r T F i).IsInvertible) ∧
    (∀ i : ℕ, i ≤ r →
      (cokernel ((completeFlagBundle r T F).inclusion i)).IsLocallyFree) := by
  classical
  obtain ⟨hz, hrank, hsplit⟩ := flag_level_induction r T F
  have hambient : ((Scheme.Modules.tensorPullback
      (completeFlagBundle r T F).projection).obj F).IsFiniteLocallyFreeOfRank r :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      ((projectiveBundleTensorPullbackIso _).app F).symm
  refine ⟨hz, ?_, ?_, ?_⟩
  · by_cases hr : r = 0
    · subst r
      exact hz.isIso (flag_rank_zero_isZero _) _
    · exact flag_top_iso r T F hr
  · intro i hi
    have := hrank i (by omega)
    have := hrank (i + 1) (by omega)
    have hstep : flagLocallySplit (completeFlagStep r T F i) := by
      intro x
      obtain ⟨U, hx, hU⟩ := hsplit i x
      let R := Scheme.Modules.restrictFunctor U.ι
      refine ⟨U, hx, IsSplitMono.mk' ⟨R.map
        ((completeFlagBundle r T F).inclusion (i + 1)) ≫
          retraction (R.map ((completeFlagBundle r T F).inclusion i)), ?_⟩⟩
      rw [← Category.assoc, ← R.map_comp]
      have hs := (Classical.choose_spec (completeFlagBundle_step_unique r T F i)).1
      change completeFlagStep r T F i ≫ _ = _ at hs
      rw [hs, IsSplitMono.id]
    have hQ : (cokernel (completeFlagStep r T F i)).IsFiniteLocallyFreeOfRank 1 := by
      simpa only [Nat.add_sub_cancel_left] using
        flag_cokernel_rank_of_local_split (completeFlagStep r T F i) (i + 1) i hstep
    have : SheafOfModules.IsInvertible.{u, u, u} (completeFlagQuotient r T F i) :=
      (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
        (completeFlagQuotient r T F i)).mpr hQ
    exact Scheme.Modules.IsInvertible.of_sheafOfModules _
  · intro i hi
    have := hrank i hi
    have hQ : (cokernel ((completeFlagBundle r T F).inclusion i)
        ).IsFiniteLocallyFreeOfRank (r - i) := flag_cokernel_rank_of_local_split
      ((completeFlagBundle r T F).inclusion i) r i (hsplit i)
    exact @SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree _ _ _ _ _ _
      (cokernel ((completeFlagBundle r T F).inclusion i)) (r - i) hQ

end AlgebraicGeometry
