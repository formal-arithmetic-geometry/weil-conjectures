/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.NativeReductionPullbackPaste
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOrdinaryCompEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerReductionPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.SectionCounit

/-! # Pasting the normalized scalar and geometric pullback comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale Opposite SheafOfModules
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]


attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exact_iso_eval_injective
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {F G : A ⥤ B} (V : B ⥤ C)
    [F.Additive] [G.Additive] [V.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e e' : F ≅ G)
    (h : ∀ K, V.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso e).hom.app K) =
      V.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso e').hom.app K)) (M : A) :
    V.map (e.hom.app M) = V.map (e'.hom.app M) := by
  apply (DerivedCategory.singleFunctor C 0).map_injective
  have ht := congrArg (fun t ↦ t ≫
    V.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app M))
      (h ((DerivedCategory.singleFunctor A 0).obj M))
  simp only [← Functor.map_comp, Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
    at ht
  simp only [Functor.map_comp] at ht
  have ht' := (cancel_epi
    (V.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M))).1 ht
  have hh := congrArg (fun t ↦ t ≫
    (V.mapDerivedCategorySingleFunctor 0).hom.app (G.obj M)) ht'
  erw [(V.mapDerivedCategorySingleFunctor 0).hom.naturality (e.hom.app M),
    (V.mapDerivedCategorySingleFunctor 0).hom.naturality (e'.hom.app M)] at hh
  exact (cancel_epi ((V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M))).1 hh

set_option maxHeartbeats 1600000 in
-- Transporting the chosen strict and finite pullback coordinates needs this budget.
private theorem ordinaryComp_normalized (s : Presentation l E) :
    SpTowerShriek.StrictOrdinaryCompNormalized l E s.base s.operations.geometry
      s.operations.ordinaryComp := by
  obtain ⟨c, hc⟩ := SpTowerShriek.strictOrdinaryComp l E s.base s.operations.geometry
  intro X Y Z f g n M
  have he : (SpTowerShriek.ev l E X n).map ((s.operations.ordinaryComp f g).hom.app M) =
      (SpTowerShriek.ev l E X n).map ((c f g).hom.app M) := by
    apply exact_iso_eval_injective (SpTowerShriek.ev l E X n)
      (s.operations.ordinaryComp f g) (c f g) ?_ M
    intro K
    have h₁ := s.operations.comp_evaluation f g n K
    have h₂ := SpTowerShriek.strictOrdinaryCompEvaluation l E s.base
      s.operations.geometry c hc f g n K
    rw [s.operations.comp_termwise f g] at h₁
    have h := (cancel_mono
      (((s.operations.geometry (f ≫ g)).pullEvaluation n).hom.app K)).1
      (h₁.trans h₂.symm)
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp] at h
    exact (cancel_epi ((SpTowerShriek.Ev l E X n).map
      ((Functor.mapDerivedCategoryCompIso (s.operations.geometry g).pull
        (s.operations.geometry f).pull).inv.app K))).1 h
  rw [he]
  exact hc f g n M

set_option maxHeartbeats 1600000 in
-- The scalar model and section-module equivalence have dependent coefficient types.
private theorem levelUnit_map (s : Presentation l E) (T : Scheme.{u}) (n : ℕ)
    {M N : Modules l E T} (a : M ⟶ N) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj M).val.obj U) :
    (((ordinaryLevel l E s T n).map a).val.app U)
        (systemModelTmul ((s.towers T).scalar
          (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
          ((spIntegralModuleEquivalence l E T).functor.obj M) U 1 x) =
      systemModelTmul ((s.towers T).scalar
        (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
        ((spIntegralModuleEquivalence l E T).functor.obj N) U 1 (a.hom.hom.app U x) := by
  let A := (s.towers T).scalar
    (spIntegralReductionScalar l E T (s.reduction T).coefficient n)
  have h := congrArg (fun z ↦ z.val.app U x)
    (A.ordinaryAdj.unit.naturality ((spIntegralModuleEquivalence l E T).functor.map a))
  change (A.ordinaryAdj.unit.app
      ((spIntegralModuleEquivalence l E T).functor.obj N)).val.app U
      (((spIntegralModuleEquivalence l E T).functor.map a).val.app U x) =
    (A.model.E.map ((spIntegralModuleEquivalence l E T).functor.map a)).val.app U
      ((A.ordinaryAdj.unit.app
        ((spIntegralModuleEquivalence l E T).functor.obj M)).val.app U x) at h
  rw [A.unit_normalized, A.unit_normalized] at h
  exact h.symm

set_option maxHeartbeats 1600000 in
-- The scalar unit is a sheaf map, independently of the chosen tensor model.
private theorem levelUnit_restrict (s : Presentation l E) (T : Scheme.{u}) (n : ℕ)
    (M : Modules l E T) {U V : T.ProEtᵒᵖ} (a : U ⟶ V)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj M).val.obj U) :
    ((ordinaryLevel l E s T n).obj M).val.map a
        (systemModelTmul ((s.towers T).scalar
          (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
          ((spIntegralModuleEquivalence l E T).functor.obj M) U 1 x) =
      systemModelTmul ((s.towers T).scalar
        (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
        ((spIntegralModuleEquivalence l E T).functor.obj M) V 1
        (M.X.obj.map a x) := by
  let A := (s.towers T).scalar
    (spIntegralReductionScalar l E T (s.reduction T).coefficient n)
  have h := PresheafOfModules.naturality_apply
    (A.ordinaryAdj.unit.app ((spIntegralModuleEquivalence l E T).functor.obj M)).val a x
  change (A.ordinaryAdj.unit.app
      ((spIntegralModuleEquivalence l E T).functor.obj M)).val.app V
      (((spIntegralModuleEquivalence l E T).functor.obj M).val.map a x) =
    (A.model.E.obj ((spIntegralModuleEquivalence l E T).functor.obj M)).val.map a
      ((A.ordinaryAdj.unit.app
        ((spIntegralModuleEquivalence l E T).functor.obj M)).val.app U x) at h
  rw [A.unit_normalized, A.unit_normalized] at h
  exact h.symm

set_option maxHeartbeats 1600000 in
-- The unit formula is transported from internal modules to underlying sections.
private theorem integralUnit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules l E Z) (V : Z.ProEt)
    (x : ((spIntegralModuleEquivalence l E Z).functor.obj M).val.obj (op V)) :
    ((CondensedRing.upperStarComp (spIntegralCondensed l E) f g).hom.app M).hom.hom.app
        (op ((Scheme.proEtaleBaseChange (f ≫ g)).obj V))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E)
          (f ≫ g)).unit.app M).hom.hom.app (op V) x) =
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj
        ((CondensedRing.upperStar (spIntegralCondensed l E) g).obj M)).X.obj.map
        ((MorphismProperty.Over.pullbackComp f g).hom.app V).op
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          ((CondensedRing.upperStar (spIntegralCondensed l E) g).obj M)).hom.hom.app
          (op ((Scheme.proEtaleBaseChange g).obj V))
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
            M).hom.hom.app (op V) x)) := by
  have h := congrArg (fun z ↦ z.hom.hom.app (op V) x)
    (CondensedRing.upperStarLowerStarAdjunction_unit_app_upperStarComp
      (spIntegralCondensed l E) f g M)
  simp only [Mod.comp_hom', CondensedRing.lowerStarComp_hom_app_hom,
    CondensedRing.lowerStar_map_hom, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ProEtale.lowerStarComp_hom_app_hom_app, ProEtale.lowerStar_map_hom_app'] at h
  exact h.symm

set_option maxHeartbeats 1600000 in
-- Use the specified adjunction conjugate, rather than an arbitrary finite compositor.
private theorem finiteUnit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (M : Scheme.proEtaleRingModules Z (SpTowerShriek.B l E Z n))
    (V : Z.ProEt) (x : M.val.obj (op V)) :
    (((Scheme.proEtaleConstantRingModulePullbackComposition f g
      (SpTowerShriek.R l E n)).choose.hom.app M).val.app
        (op ((Scheme.proEtaleBaseChange (f ≫ g)).obj V)))
        (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n)
          (f ≫ g)).unit.app M).val.app (op V) x) =
      ((Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).obj
        ((Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) g).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp f g).hom.app V).op
        (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
          ((Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) g).obj M)).val.app
          (op ((Scheme.proEtaleBaseChange g).obj V))
          (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) g).unit.app
            M).val.app (op V) x)) := by
  let c := (Scheme.proEtaleConstantRingModulePullbackComposition f g
    (SpTowerShriek.R l E n)).choose
  let d := (Scheme.proEtaleConstantRingModulePullbackComposition f g
    (SpTowerShriek.R l E n)).choose_spec.choose
  have hd : conjugateIsoEquiv
      ((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) g).comp
        (Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f))
      (Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) (f ≫ g)) c = d :=
    (Scheme.proEtaleConstantRingModulePullbackComposition f g
      (SpTowerShriek.R l E n)).choose_spec.choose_spec.2
  have h := unit_conjugateEquiv
    ((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) g).comp
      (Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f))
    (Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) (f ≫ g)) c.hom M
  rw [← conjugateIsoEquiv_apply_hom, hd, Adjunction.comp_unit_app] at h
  have hs := congrArg (fun z ↦ z.val.app (op V) x) h
  have ds := (Scheme.proEtaleConstantRingModulePullbackComposition f g
    (SpTowerShriek.R l E n)).choose_spec.choose_spec.1
      ((Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).obj
        ((Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) g).obj M)) V
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hs
  change (d.hom.app
      ((Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).obj
        ((Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) g).obj M))).val.app
      (op V)
      ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) g).obj M)).val.app
        (op ((Scheme.proEtaleBaseChange g).obj V)))
        (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) g).unit.app
          M).val.app (op V) x)) =
    (c.hom.app M).val.app (op ((Scheme.proEtaleBaseChange (f ≫ g)).obj V))
      (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) (f ≫ g)).unit.app
        M).val.app (op V) x) at hs
  rw [ds] at hs
  exact hs.symm

set_option maxHeartbeats 2400000 in
-- Pasting evaluates through several fixed equivalences of module presentations.
private theorem levelMap_paste (s : Presentation l E) (q : ReductionGeometry l E s)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules l E Z) (n : ℕ) :
    ordinaryPullLevelMap l E s q.evaluation (f ≫ g)
        (nativeReductionOrdinaryPaste l E s q f g) M n =
      (ordinaryLevel l E s X n).map
          ((CondensedRing.upperStarComp (spIntegralCondensed l E) f g).hom.app M) ≫
        ordinaryPullLevelMap l E s q.evaluation f (q.pullback f).ordinary
          ((CondensedRing.upperStar (spIntegralCondensed l E) g).obj M) n ≫
        (Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).map
          (ordinaryPullLevelMap l E s q.evaluation g (q.pullback g).ordinary M n) ≫
        (Scheme.proEtaleConstantRingModulePullbackComposition f g
          (SpTowerShriek.R l E n)).choose.inv.app ((ordinaryLevel l E s Z n).obj M) := by
  have hc := ordinaryComp_normalized l E s f g n ((ordinaryReduction l E s Z).obj M)
  simp only [ordinaryPullLevelMap, nativeReductionOrdinaryPaste, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.map_comp, Category.assoc]
  erw [reassoc_of% hc]
  erw [← (ordinaryReductionEvaluation l E s q.evaluation X n).inv.naturality_assoc]
  erw [((s.operations.geometry f).ordinaryPullEvaluation n).hom.naturality_assoc]
  have hn := (Scheme.proEtaleConstantRingModulePullbackComposition f g
    (SpTowerShriek.R l E n)).choose.inv.naturality
      ((ordinaryReductionEvaluation l E s q.evaluation Z n).hom.app M)
  erw [← hn]
  simp only [Functor.comp_map]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Resolve instances across the equivalent integral and section-module presentations.
set_option maxHeartbeats 2400000 in
-- Both scalar and geometric units retain the actual section-module coordinates.
/-- The pasted ordinary comparison equals the normalized comparison of the composite.
Source: normalized scalar/pullback construction, paragraphs (2)--(3).
Proof: evaluate at level n and cancel the fixed reduction evaluation isomorphisms.
The ordinary system compositor evaluates to the finite geometric compositor, by
its termwise localization formula and comp_evaluation, tested on degree-zero complexes.
Transpose the level maps through the scalar and geometric adjunctions. The given
generator formulas identify their transposes on every local section. Naturality
of the scalar unit and the composite-geometric-unit formula identify the iterated
transpose with the direct transpose. Injectivity of the two Hom bijections gives
levelwise equality. Every section of a strict system has a level, so these level
identities give equality of ordinary morphisms, hence of the natural isomorphisms.
(blueprint: lem-dla1-native-reduction-ordinary-composition). -/
theorem nativeReductionOrdinaryPaste_eq (s : Presentation l E)
    (q : ReductionGeometry l E s) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    nativeReductionOrdinaryPaste l E s q f g = (q.pullback (f ≫ g)).ordinary := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have he (n : ℕ) : ordinaryPullLevelMap l E s q.evaluation (f ≫ g)
      (nativeReductionOrdinaryPaste l E s q f g) M n =
      ordinaryPullLevelMap l E s q.evaluation (f ≫ g)
        (q.pullback (f ≫ g)).ordinary M n := by
    apply scalar_geometric_hom_ext l E s (f ≫ g) M n
    intro V x
    let pg := CondensedRing.upperStar (spIntegralCondensed l E) g
    let fp := Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f
    let lg := ordinaryPullLevelMap l E s q.evaluation g (q.pullback g).ordinary M n
    let ty := systemModelTmul ((s.towers Y).scalar
      (spIntegralReductionScalar l E Y (s.reduction Y).coefficient n)).model
      ((spIntegralModuleEquivalence l E Y).functor.obj (pg.obj M))
      (op ((Scheme.proEtaleBaseChange g).obj V)) 1
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
        M).hom.hom.app (op V) x)
    have hu := congrArg (fun z ↦ z.val.app
        (op ((Scheme.proEtaleBaseChange g).obj V)) ty)
      ((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.naturality lg)
    change (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) g).obj
          ((ordinaryLevel l E s Z n).obj M))).val.app
          (op ((Scheme.proEtaleBaseChange g).obj V)))
          (lg.val.app (op ((Scheme.proEtaleBaseChange g).obj V)) ty) =
      ((fp.map lg).val.app
        (op ((Scheme.proEtaleBaseChange f).obj ((Scheme.proEtaleBaseChange g).obj V))))
        ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
          ((ordinaryLevel l E s Y n).obj (pg.obj M))).val.app
            (op ((Scheme.proEtaleBaseChange g).obj V))) ty) at hu
    rw [levelMap_paste]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    rw [levelUnit_map, integralUnit_comp]
    have hr := levelUnit_restrict l E s X n
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj (pg.obj M))
      ((MorphismProperty.Over.pullbackComp f g).hom.app V).op
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        (pg.obj M)).hom.hom.app (op ((Scheme.proEtaleBaseChange g).obj V))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) g).unit.app
          M).hom.hom.app (op V) x))
    erw [← hr]
    erw [PresheafOfModules.naturality_apply
      (ordinaryPullLevelMap l E s q.evaluation f (q.pullback f).ordinary (pg.obj M) n).val
      ((MorphismProperty.Over.pullbackComp f g).hom.app V).op]
    erw [(q.pullback f).generators (pg.obj M) n ((Scheme.proEtaleBaseChange g).obj V)]
    erw [PresheafOfModules.naturality_apply (fp.map lg).val
      ((MorphismProperty.Over.pullbackComp f g).hom.app V).op]
    erw [← hu]
    dsimp only [lg, ty, pg]
    erw [(q.pullback g).generators M n V x]
    erw [← finiteUnit_comp l E f g n ((ordinaryLevel l E s Z n).obj M) V]
    erw [(q.pullback (f ≫ g)).generators M n V x]
    let cb := (Scheme.proEtaleConstantRingModulePullbackComposition f g
      (SpTowerShriek.R l E n)).choose
    have hb := Iso.hom_inv_id_app cb ((ordinaryLevel l E s Z n).obj M)
    have ht := congrArg (fun a ↦ a.val.app
        (op ((Scheme.proEtaleBaseChange (f ≫ g)).obj V))
        ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n)
          (f ≫ g)).unit.app ((ordinaryLevel l E s Z n).obj M)).val.app (op V))
          (systemModelTmul ((s.towers Z).scalar
            (spIntegralReductionScalar l E Z (s.reduction Z).coefficient n)).model
            ((spIntegralModuleEquivalence l E Z).functor.obj M) (op V) 1 x))) hb
    simp only [cb, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] at ht
    exact ht
  have hl (n : ℕ) :
      (SpTowerShriek.ev l E X n).map
          ((nativeReductionOrdinaryPaste l E s q f g).hom.app M) =
        (SpTowerShriek.ev l E X n).map ((q.pullback (f ≫ g)).ordinary.hom.app M) := by
    apply (cancel_epi ((ordinaryReductionEvaluation l E s q.evaluation X n).inv.app _)).1
    apply (cancel_mono
      (((s.operations.geometry (f ≫ g)).ordinaryPullEvaluation n).hom.app
        ((ordinaryReduction l E s Z).obj M) ≫
      (Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) (f ≫ g)).map
        ((ordinaryReductionEvaluation l E s q.evaluation Z n).hom.app M))).1
    simpa only [ordinaryPullLevelMap, Category.assoc] using he n
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rcases U with ⟨n, V⟩
  ext x
  exact congrArg (fun a ↦ a.val.app (op V) x) (hl n)

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
