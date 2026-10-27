/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups D9, K7
-/
module

public import Sheaf.Paper.ClosedFibreModuleEvaluation
public import Sheaf.Paper.ClosedTorsionRigiditySerreTransfer
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtaleDerived
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GermComp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor

/-! # Derived evaluation and restriction after weakly etale localization

Source: Stacks Project, Tags 0D6F, 0D6G and 098K.
(blueprint: lem-sfb-weakly-etale-derived-evaluation-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

open MonoidalCategory MonoidalClosed Functor.LaxMonoidal

private lemma projection_of_closed
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    {L : D ⥤ C} {S : C ⥤ D} (adj : L ⊣ S) [S.Monoidal]
    (A : C) (M : D) [IsIso (ihomComparison S A).natTrans] :
    IsIso (adj.projectionFormulaMap A M) := by
  have := Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison adj A
  change IsIso ((Functor.Monoidal.projectionMap adj A).app M)
  infer_instance

private lemma derived_pullback_iso
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [P.PreservesKInjectiveComplexes]
    {F : C ⥤ D} {F' : C' ⥤ D} [F.Additive] [F'.Additive]
    (α : F ⟶ P ⋙ F') [IsIso α] (M : DerivedCategory C) :
    IsIso ((Functor.rightDerivedPullback P α).app M) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  have hi : IsIso ((Functor.rightDerivedPullback P α).app (DerivedCategory.Q.obj I)) := by
    have h := Functor.rightDerivedFunctorUnitQ_rightDerivedPullback_app' P α I
    have : IsIso (F.rightDerivedFunctorUnitQ I) := by
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have : IsIso (F'.rightDerivedFunctorUnitQ ((P.mapHomologicalComplex (.up ℤ)).obj I)) := by
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have : IsIso ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I) := by
      have h : ∀ n, IsIso (((NatTrans.mapHomologicalComplex α (.up ℤ)).app I).f n) := by
        intro n
        change IsIso (α.app (I.X n))
        infer_instance
      exact HomologicalComplex.Hom.isIso_of_components _
    have : IsIso (F.rightDerivedFunctorUnitQ I ≫
        (Functor.rightDerivedPullback P α).app (DerivedCategory.Q.obj I)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left (F.rightDerivedFunctorUnitQ I) _
  have hn := (Functor.rightDerivedPullback P α).naturality e.hom
  have : IsIso ((Functor.rightDerivedPullback P α).app M ≫
      (P.mapDerivedCategory ⋙ F'.rightDerivedFunctor).map e.hom) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right ((Functor.rightDerivedPullback P α).app M)
    ((P.mapDerivedCategory ⋙ F'.rightDerivedFunctor).map e.hom)

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private lemma module_weaklyEtale_preservesKInjective
    {X T : Scheme.{u}} (b : T ⟶ X) [WeaklyEtale b] :
    (upperStar Λ b).PreservesKInjectiveComplexes := by
  let adj := ProEtale.weaklyEtaleLowerShriekAdjunction Ab.{u + 1} b
  have : adj.HasProjectionFormula := by
    constructor
    intro A M
    have : IsIso (ihomComparison (ProEtale.upperStar Ab.{u + 1} b) A).natTrans :=
      ProEtale.isIso_ihomComparison_upperStar Ab.{u + 1} b A
    exact projection_of_closed adj A M
  let L := Mod.comap (condensedPullbackHom Λ b) ⋙ adj.mapModLeft (condensedRingObj Λ X)
  let a : L ⊣ upperStar Λ b :=
    ((Mod.restrictCoextendAdjunction (condensedPullbackHom Λ b)).comp
      adj.mapModLeftAdjunction).ofNatIsoRight
      (Functor.isoWhiskerLeft
        ((ProEtale.upperStar Ab.{u + 1} b).mapMod (condensedRingObj Λ X))
        (Mod.extendScalarsIsoCoextendScalars (condensedPullbackHom Λ b)).symm)
  have : PreservesFiniteLimits L := by dsimp [L]; infer_instance
  have : PreservesFiniteColimits L := by dsimp [L]; infer_instance
  have : L.Additive := a.left_adjoint_additive
  have : L.PreservesHomology := {}
  exact a.preservesKInjectiveComplexes

private noncomputable def upper_forget_iso
    {X T : Scheme.{u}} (b : T ⟶ X) :
    upperStar Λ b ⋙ Mod.forget (condensedRingObj Λ T) ≅
      Mod.forget (condensedRingObj Λ X) ⋙ ProEtale.upperStar Ab.{u + 1} b :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft
      ((ProEtale.upperStar Ab.{u + 1} b).mapMod (condensedRingObj Λ X))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ b)))
    (Mod.forget (condensedRingObj Λ T))

private lemma sections_forget
    {X Z : Scheme.{u}} (a : Z ⟶ X) (U : X.ProEt)
    (φ : Z ⟶ U.left) (hφ : φ ≫ U.hom = a)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (closedFibreModuleSectionsRestriction Λ a U φ hφ).app M ≫
        ((upper_forget_iso Λ a).hom.app M).hom.app (op (Scheme.ProEt.mk (𝟙 Z))) =
      ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} a).unit.app M.X).hom.app (op U) ≫
        ((ProEtale.upperStar Ab.{u + 1} a).obj M.X).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift φ (𝟙 Z) (hφ.trans (Category.id_comp a).symm))
            (pullback.lift_snd _ _ _)).op := by
  let P := ((ProEtale.upperStar Ab.{u + 1} a).mapMod (condensedRingObj Λ X)).obj M
  let q := (upper_forget_iso Λ a).hom.app M
  let s : Scheme.ProEt.mk (𝟙 Z) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj U :=
    MorphismProperty.Over.homMk
      (pullback.lift φ (𝟙 Z) (hφ.trans (Category.id_comp a).symm))
      (pullback.lift_snd _ _ _)
  have hu := upperStarLowerStarAdjunction_homEquiv_hom Λ a M
    ((upperStar Λ a).obj M) (𝟙 _)
  rw [Adjunction.homEquiv_id, Mod.id_hom'] at hu
  have hq : Mod.extendUnitHom (condensedPullbackHom Λ a) P ≫ q = 𝟙 _ :=
    extendUnitHom_extendScalarsIsoComapInv_hom_app Λ a P
  have hn := q.hom.naturality s.op
  change ((upperStarLowerStarAdjunction Λ a).unit.app M).hom.hom.app (op U) ≫
      ((upperStar Λ a).obj M).X.obj.map s.op ≫ q.hom.app _ = _
  erw [hn]
  have hu' := congrArg (fun f ↦ f.hom.app (op U)) hu
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ProEtale.lowerStar_map_hom_app, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app] at hu'
  rw [hu']
  simp only [Category.assoc]
  change ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} a).unit.app M.X).hom.app
      (op U) ≫ (Mod.extendUnitHom (condensedPullbackHom Λ a) P).hom.app _ ≫
      q.hom.app _ ≫ P.X.obj.map s.op = _
  have he := congrArg (fun f ↦ f.hom.app
    (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj U))) hq
  have he' : (Mod.extendUnitHom (condensedPullbackHom Λ a) P).hom.app
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj U)) ≫
        q.hom.app _ = 𝟙 _ := he
  erw [reassoc_of% he']
  rfl

private lemma localization_sections_iso
    {X T : Scheme.{u}} (b : T ⟶ X) [WeaklyEtale b] :
    IsIso (closedFibreModuleSectionsRestriction Λ b (Scheme.ProEt.mk b) (𝟙 T)
      (Category.id_comp b)) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro M
  let s : Scheme.ProEt.mk (𝟙 T) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ b).obj (Scheme.ProEt.mk b) :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 T) (𝟙 T) (by simp))
      (pullback.lift_snd _ _ _)
  let r : Scheme.ProEt.mk b ≅
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale b)).obj
        (Scheme.ProEt.mk (𝟙 T)) :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by exact Category.id_comp b)
  let e := ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} b inferInstance
  have hg := ProEtale.germ_comp_upperStarIsoLocalizationRestriction
    Ab.{u + 1} b inferInstance M.X s
  rw [ProEtale.germ, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc] at hg
  have hm : IsIso
      (M.X.obj.map (((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale b)).map s ≫
        (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ b
          inferInstance trivial).counit.app (Scheme.ProEt.mk b)).op)) := by
    have he : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale b)).map s ≫
        (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ b
          inferInstance trivial).counit.app (Scheme.ProEt.mk b) = r.inv := by
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift (𝟙 T) (𝟙 T) _ ≫ pullback.fst b b = 𝟙 T
      simp
    rw [he]
    infer_instance
  have hf := sections_forget Λ b (Scheme.ProEt.mk b) (𝟙 T) (Category.id_comp b) M
  have hh : IsIso ((closedFibreModuleSectionsRestriction Λ b (Scheme.ProEt.mk b)
        (𝟙 T) (Category.id_comp b)).app M ≫
      ((upper_forget_iso Λ b).hom.app M).hom.app (op (Scheme.ProEt.mk (𝟙 T))) ≫
      (e.hom.app M.X).hom.app (op (Scheme.ProEt.mk (𝟙 T)))) := by
    rw [← Category.assoc, hf]
    rw [Category.assoc]
    exact hg.symm ▸ hm
  have : IsIso (((upper_forget_iso Λ b).hom.app M).hom.app
      (op (Scheme.ProEt.mk (𝟙 T)))) := by infer_instance
  have : IsIso ((closedFibreModuleSectionsRestriction Λ b (Scheme.ProEt.mk b)
      (𝟙 T) (Category.id_comp b)).app M ≫
        ((upper_forget_iso Λ b).hom.app M).hom.app (op (Scheme.ProEt.mk (𝟙 T)))) :=
    IsIso.of_isIso_comp_right _
      ((e.hom.app M.X).hom.app (op (Scheme.ProEt.mk (𝟙 T))))
  exact IsIso.of_isIso_comp_right _
    (((upper_forget_iso Λ b).hom.app M).hom.app (op (Scheme.ProEt.mk (𝟙 T))))

private lemma module_unit_comp
    {X T Z : Scheme.{u}} (b : T ⟶ X) (t : Z ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarLowerStarAdjunction Λ (t ≫ b)).unit.app M ≫
        (lowerStar Λ (t ≫ b)).map ((upperStarComp Λ t b).hom.app M) =
      (upperStarLowerStarAdjunction Λ b).unit.app M ≫
        (lowerStar Λ b).map
          ((upperStarLowerStarAdjunction Λ t).unit.app ((upperStar Λ b).obj M)) ≫
        (lowerStarComp Λ t b).hom.app ((upperStar Λ t).obj ((upperStar Λ b).obj M)) := by
  have hu := unit_conjugateEquiv
    ((upperStarLowerStarAdjunction Λ b).comp (upperStarLowerStarAdjunction Λ t))
    (upperStarLowerStarAdjunction Λ (t ≫ b)) (upperStarComp Λ t b).hom M
  rw [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarComp,
    Adjunction.comp_unit_app] at hu
  rw [← hu, Category.assoc]
  rfl

private lemma sections_comp
    {X T Z : Scheme.{u}} (b : T ⟶ X) [WeaklyEtale b] (t : Z ⟶ T) :
    closedFibreModuleSectionsRestriction Λ (t ≫ b) (Scheme.ProEt.mk b) t rfl ≫
        Functor.whiskerRight (upperStarComp Λ t b).hom
          (closedFibreModuleEvaluation Λ Z (Scheme.ProEt.mk (𝟙 Z))) =
      closedFibreModuleSectionsRestriction Λ b (Scheme.ProEt.mk b) (𝟙 T)
          (Category.id_comp b) ≫
        Functor.whiskerLeft (upperStar Λ b) (torsionRigiditySectionsRestriction Λ t) := by
  apply NatTrans.ext
  funext M
  let U := Scheme.ProEt.mk b
  let B := MorphismProperty.Over.pullback @WeaklyEtale ⊤ b
  let A := MorphismProperty.Over.pullback @WeaklyEtale ⊤ (t ≫ b)
  let R := MorphismProperty.Over.pullback @WeaklyEtale ⊤ t
  let sb : Scheme.ProEt.mk (𝟙 T) ⟶ B.obj U :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 T) (𝟙 T) (by simp [U]))
      (pullback.lift_snd _ _ _)
  let sa : Scheme.ProEt.mk (𝟙 Z) ⟶ A.obj U :=
    MorphismProperty.Over.homMk (pullback.lift t (𝟙 Z) (by simp [U]))
      (pullback.lift_snd _ _ _)
  let st : Scheme.ProEt.mk (𝟙 Z) ⟶ R.obj (Scheme.ProEt.mk (𝟙 T)) :=
    MorphismProperty.Over.homMk (pullback.lift t (𝟙 Z) (by simp))
      (pullback.lift_snd _ _ _)
  let N := (upperStar Λ t).obj ((upperStar Λ b).obj M)
  have hE := congrArg (fun f ↦ f.hom.hom.app (op U)) (module_unit_comp Λ b t M)
  simp only [Mod.comp_hom', lowerStar_map_hom, lowerStarComp_hom_app_hom,
    ProEtale.lowerStar_map_hom_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app] at hE
  have n₁ := ((upperStarComp Λ t b).hom.app M).hom.hom.naturality sa.op
  have n₃ := ((upperStarLowerStarAdjunction Λ t).unit.app
    ((upperStar Λ b).obj M)).hom.hom.naturality sb.op
  have ht : sa ≫ (MorphismProperty.Over.pullbackComp t b).hom.app U = st ≫ R.map sb := by
    apply MorphismProperty.Over.Hom.ext
    change sa.left ≫ ((MorphismProperty.Over.pullbackComp t b).hom.app U).left =
      st.left ≫ (R.map sb).left
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [sa, st, sb, R, B, A, U]
    · simp [sa, st, sb, R, B, A, U]
  change ((upperStarLowerStarAdjunction Λ (t ≫ b)).unit.app M).hom.hom.app (op U) ≫
      ((upperStar Λ (t ≫ b)).obj M).X.obj.map sa.op ≫
      ((upperStarComp Λ t b).hom.app M).hom.hom.app (op (Scheme.ProEt.mk (𝟙 Z))) =
    ((upperStarLowerStarAdjunction Λ b).unit.app M).hom.hom.app (op U) ≫
      ((upperStar Λ b).obj M).X.obj.map sb.op ≫
      ((upperStarLowerStarAdjunction Λ t).unit.app ((upperStar Λ b).obj M)).hom.hom.app
        (op (Scheme.ProEt.mk (𝟙 T))) ≫ N.X.obj.map st.op
  rw [n₁]
  erw [reassoc_of% hE]
  rw [reassoc_of% n₃]
  rw [ProEtale.lowerStarComp_hom_app_hom_app]
  change ((upperStarLowerStarAdjunction Λ b).unit.app M).hom.hom.app (op U) ≫
      ((upperStarLowerStarAdjunction Λ t).unit.app ((upperStar Λ b).obj M)).hom.hom.app
        (op (B.obj U)) ≫ N.X.obj.map
          ((MorphismProperty.Over.pullbackComp t b).hom.app U).op ≫ N.X.obj.map sa.op =
    ((upperStarLowerStarAdjunction Λ b).unit.app M).hom.hom.app (op U) ≫
      ((upperStarLowerStarAdjunction Λ t).unit.app ((upperStar Λ b).obj M)).hom.hom.app
        (op (B.obj U)) ≫ N.X.obj.map (R.map sb).op ≫ N.X.obj.map st.op
  have hm : N.X.obj.map ((MorphismProperty.Over.pullbackComp t b).hom.app U).op ≫
        N.X.obj.map sa.op = N.X.obj.map (R.map sb).op ≫ N.X.obj.map st.op := by
    rw [← Functor.map_comp, ← op_comp, ht, op_comp, Functor.map_comp]
  rw [hm]

/-- Localization at a weakly etale object identifies the actual derived section restriction
with restriction on its scheme. Source: Stacks Project, Tags 0D6F and 0D6G, using the
small pro-etale slice equivalence of Tag 098K.
(blueprint: lem-sfb-weakly-etale-derived-evaluation-restriction).

Proof. Let b:T -> X be weakly etale. The small pro-etale site of T is the slice of the
small pro-etale site of X at b. Restriction of module sheaves to that slice is exact,
has exact extension by zero as a left adjoint, and hence preserves K-injective complexes.
Its comparison with b-star is the canonical isomorphism of inverse images, including
the coefficient-ring comparison. Sections of the restricted module on T are sections
of the original module at b. On a K-injective representative I of K this identifies the
derived localization map with the termwise section isomorphism, so that map is invertible.
For t:Z -> T and a=t;b, the adjunction composition identity identifies a-star with
b-star followed by t-star. The underived unit followed by restriction along (t,id) is
the composite of localization and the terminal-object restriction on T. The composition
identity for rightDerivedPullback gives the same factorization in the derived category,
up to the invertible inverse-image composition comparison. Cancel that comparison and
the localization isomorphism. This proves the equivalence, including empty schemes and
arbitrary unbounded complexes; no properness or coefficient finiteness is used. -/
theorem weaklyEtale_derived_evaluation_restriction_iff
    {X T Z : Scheme.{u}} (b : T ⟶ X) [WeaklyEtale b] (t : Z ⟶ T)
    (a : Z ⟶ X) (ha : t ≫ b = a)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso ((closedFibreModuleDerivedRestriction Λ a (Scheme.ProEt.mk b) t ha).app K) ↔
      IsIso ((torsionRigidityDerivedRestriction Λ t).app
        ((upperStar Λ b).mapDerivedCategory.obj K)) := by
  subst a
  let P := upperStar Λ b
  let P' := upperStar Λ t
  let P'' := upperStar Λ (t ≫ b)
  let F := closedFibreModuleEvaluation Λ X (Scheme.ProEt.mk b)
  let F' := condensedModuleSections Λ T
  let F'' := condensedModuleSections Λ Z
  let α := closedFibreModuleSectionsRestriction Λ b (Scheme.ProEt.mk b) (𝟙 T)
    (Category.id_comp b)
  let α' := torsionRigiditySectionsRestriction Λ t
  let α'' := closedFibreModuleSectionsRestriction Λ (t ≫ b) (Scheme.ProEt.mk b) t rfl
  have : P.PreservesKInjectiveComplexes := module_weaklyEtale_preservesKInjective Λ b
  have : IsIso α := localization_sections_iso Λ b
  have : IsIso ((Functor.rightDerivedPullback P α).app K) :=
    derived_pullback_iso P α K
  have h := Functor.rightDerivedPullback_comp P P' P'' (upperStarComp Λ t b)
    α α' α'' (sections_comp Λ b t) K
  change IsIso ((Functor.rightDerivedPullback P'' α'').app K) ↔
    IsIso ((Functor.rightDerivedPullback P' α').app (P.mapDerivedCategory.obj K))
  rw [← isIso_comp_right_iff _
    (F''.rightDerivedFunctor.map
      ((Functor.mapDerivedCategoryNatIso (upperStarComp Λ t b) ≪≫
        Functor.mapDerivedCategoryCompIso P P').hom.app K)), h,
    isIso_comp_left_iff]

end AlgebraicGeometry.ProEtale.CondensedRing
