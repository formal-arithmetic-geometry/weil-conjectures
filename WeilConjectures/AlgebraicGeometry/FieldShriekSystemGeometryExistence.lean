/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemModels
import all WeilConjectures.AlgebraicGeometry.SmoothPurityStrictOpenTensorCoordinates
import all WeilConjectures.AlgebraicGeometry.VaryingRingOperations
import WeilConjectures.AlgebraicGeometry.SemilinearNaturalIsoAssembly
import all WeilConjectures.SixFunctors.SystemProperOpenScalarData
import all WeilConjectures.SixFunctors.SemilinearProperOpenEvaluationSupport
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralFiniteFree
import all WeilConjectures.NumberTheory.Padics.LocalFieldCoefficientStages
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.CategoryTheory.ConstantFiniteFreeSectionBasis
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
import all WeilConjectures.SixFunctors.ExactLocalizationInverseMate

/-! # Normalized geometric comparisons for prescribed coefficient models

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md (2)
(blueprint: lem-route-field-shriek-system-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u t v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

open CategoryTheory.Limits Opposite WeilConjectures.SemilinearSections

attribute [local implicit_reducible] CategoryTheory.TwoSquare
  CategoryTheory.Functor.mapHomologicalComplex
  AlgebraicGeometry.ProEtale.VaryingRing.push
  AlgebraicGeometry.ProEtale.VaryingRing.baseChange
  AlgebraicGeometry.ProEtale.spCoefficientCommRings
  AlgebraicGeometry.ProEtale.SpTowerShriek.tau
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  WeilConjectures.SemilinearSections.evaluation
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
  AlgebraicGeometry.ProEtale.StrictTower.modulePullback
  AlgebraicGeometry.ProEtale.StrictTower.moduleDirectImage
  AlgebraicGeometry.ProEtale.StrictTower.constantRingIso
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
attribute [local irreducible] CategoryTheory.constantSheaf Padic
  Padic.coefficientExtensionIntegers
  WeilConjectures.SemilinearSections.transition
  WeilConjectures.SemilinearSections.coefficientMap
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap

attribute [local implicit_reducible] WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings

attribute [local instance] VaryingRing.prodOpenContinuous

section PushCoordinates

open SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option maxHeartbeats 1600000 in
-- Normalize the section types of the two sequence rings.
private structure PushModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (σX : ∀ n, B l E X (n + 1) ⟶ B l E X n)
    (σY : ∀ n, B l E Y (n + 1) ⟶ B l E Y n) where
  ringMap : ring (coefficientSequenceTopology (ProEt.topology Y))
      (systemRing (ProEt.topology Y) (B l E Y) σY) ⟶
    ((VaryingRing.baseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X))).obj
        (ring (coefficientSequenceTopology (ProEt.topology X))
          (systemRing (ProEt.topology X) (B l E X) σX))
  ringMap_app : ∀ V, ringMap.hom.app V = VaryingRing.ringMapApp (VR l E) f V
  openTranspose : ∀ [IsOpenImmersion f], IsIso
    ((((VaryingRing.prodAdj (VaryingRing.openAdj f)).sheafPushforwardContinuous
      (E := RingCat.{u + 1}) (coefficientSequenceTopology (ProEt.topology X))
      (coefficientSequenceTopology (ProEt.topology Y))).homEquiv _ _).symm ringMap)
  push : SS l E X σX ⥤ SS l E Y σY
  push_eq : push = SheafOfModules.pushforward ringMap
  evaluation : ∀ n, push ⋙ EE l E Y σY n ≅
    EE l E X σX n ⋙ proEtaleConstantRingPushforward (R l E n) f
  horizontal : ∀ (M : SS l E X σX) {m n : ℕ} (h : n ≤ m) (V : Y.ProEtᵒᵖ)
    (x : ((EE l E Y σY m).obj (push.obj M)).val.obj V),
    ((evaluation n).hom.app M).val.app V (HS l E Y σY h (push.obj M) V x) =
      HS l E X σX h M (chart f V) (((evaluation m).hom.app M).val.app V x)
  sections : ∀ (M : SS l E X σX) (n : ℕ) (V : Y.ProEtᵒᵖ)
    (x : ((EE l E Y σY n).obj (push.obj M)).val.obj V),
    HEq (((evaluation n).hom.app M).val.app V x) x

set_option maxHeartbeats 1600000 in
-- Comparing the constant coefficient sequence rings requires extra reduction.
private theorem canonicalPushModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (σX : ∀ n, B l E X (n + 1) ⟶ B l E X n)
    (σY : ∀ n, B l E Y (n + 1) ⟶ B l E Y n)
    (hX : σX = VaryingRing.coefficientTransition (VR l E) (VM l E) X)
    (hY : σY = VaryingRing.coefficientTransition (VR l E) (VM l E) Y) :
    Nonempty (PushModel l E f σX σY) := by
  subst σX σY
  refine ⟨{
    ringMap := VaryingRing.ringMap (VR l E) (VM l E) f
    ringMap_app := fun _ ↦ rfl
    openTranspose := by
      intro hf
      exact VaryingRing.openRingTranspose_isIso (VR l E) (VM l E) f
    push := VaryingRing.push (VR l E) (VM l E) f
    push_eq := rfl
    evaluation := VaryingRing.moduleEvalP (VR l E) (VM l E) f
    horizontal := canonicalPushHorizontal (VR l E) (VM l E) f
    sections := ?_ }⟩
  intro M n V x
  exact heq_of_eq
    ((VaryingRing.moduleEvalP_existsUnique (VR l E) (VM l E) f n).choose_spec.1
      M V.unop x)

private def pushLevelComparison (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : Geometry l E b f) (c : PushModel l E f (tau l E X) (tau l E Y)) (n : ℕ) :
    g.push ⋙ ev l E Y n ≅ c.push ⋙ ev l E Y n :=
  g.ordinaryPushEvaluation n ≪≫ (c.evaluation n).symm

set_option maxHeartbeats 1600000 in
-- Compare the section coordinates of the two normalized pushforwards.
private theorem pushLevelComparison_horizontal (b : Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : Geometry l E b f)
    (c : PushModel l E f (tau l E X) (tau l E Y))
    (M : S l E X) {m n : ℕ} (h : n ≤ m) :
    (horizontal l E Y h).app (g.push.obj M) ≫
        (restrict l E Y h).map ((pushLevelComparison l E b g c n).hom.app M) =
      (pushLevelComparison l E b g c m).hom.app M ≫
        (horizontal l E Y h).app (c.push.obj M) := by
  have hd (k : ℕ) : (pushLevelComparison l E b g c k).hom.app M ≫
      (c.evaluation k).hom.app M = (g.ordinaryPushEvaluation k).hom.app M := by
    simp only [pushLevelComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply (cancel_mono ((restrict l E Y h).map ((c.evaluation n).hom.app M))).mp
  rw [Category.assoc, ← Functor.map_comp, hd]
  ext V x
  have hg := push_horizontal l E f b g M h V x
  have hc := c.horizontal M h V
    (((pushLevelComparison l E b g c m).hom.app M).val.app V x)
  have hm := congrArg (fun a ↦ a.val.app V x) (hd m)
  change ((c.evaluation m).hom.app M).val.app V
      (((pushLevelComparison l E b g c m).hom.app M).val.app V x) =
    ((g.ordinaryPushEvaluation m).hom.app M).val.app V x at hm
  rw [hm] at hc
  change ((g.ordinaryPushEvaluation n).hom.app M).val.app V
      (HS l E Y (tau l E Y) h (g.push.obj M) V x) =
    ((c.evaluation n).hom.app M).val.app V
      (HS l E Y (tau l E Y) h (c.push.obj M) V
        (((pushLevelComparison l E b g c m).hom.app M).val.app V x))
  exact hg.trans hc.symm

private theorem pushComparison_exists (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : Geometry l E b f) (c : PushModel l E f (tau l E X) (tau l E Y)) :
    ∃ d : g.push ≅ c.push, ∀ (M : S l E X) (n : ℕ),
      (ev l E Y n).map (d.hom.app M) =
        (pushLevelComparison l E b g c n).hom.app M := by
  exact naturalIsoOfEvaluation_exists.{u, u + 1} (ProEt.topology Y) (B l E Y) (tau l E Y)
    g.push c.push (pushLevelComparison l E b g c)
    (fun M _ _ h ↦ pushLevelComparison_horizontal l E b g c M h)

private theorem transportPushSections
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f) (n : ℕ)
    (B' : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τ' : ∀ k, B' (k + 1) ⟶ B' k)
    (hB : B' = SpTowerShriek.B l E X) (hτ : HEq τ' (SpTowerShriek.tau l E X))
    (G : SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ' ⥤ SpTowerShriek.S l E Y)
    (hG : HEq g.push G)
    (q : Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (B' n),
      Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (B' n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n), L ⊣ P)
    (hq : HEq q
      (⟨proEtaleConstantRingPullback (SpTowerShriek.R l E n) f,
        proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f,
        proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n),
          Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n) ⥤
            SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n), L ⊣ P))
    (e : G ⋙ SpTowerShriek.ev l E Y n ≅
      SemilinearSections.evaluation.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) B' τ' n ⋙ q.2.1)
    (he : HEq (g.ordinaryPushEvaluation n) e)
    (hs : ∀ N U (x : ((SpTowerShriek.ev l E Y n).obj (G.obj N)).val.obj U),
      HEq ((e.hom.app N).val.app U x) x) :
    ∀ N U (x : ((SpTowerShriek.ev l E Y n).obj (g.push.obj N)).val.obj U),
      HEq (((g.ordinaryPushEvaluation n).hom.app N).val.app U x) x := by
  subst B'
  cases eq_of_heq hτ
  cases eq_of_heq hG
  cases eq_of_heq hq
  cases eq_of_heq he
  exact hs

private theorem pushEvaluationSections
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f) (n : ℕ)
    (N : SpTowerShriek.S l E X) (U : Y.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E Y n).obj (g.push.obj N)).val.obj U) :
    HEq (((g.ordinaryPushEvaluation n).hom.app N).val.app U x) x := by
  exact transportPushSections l E g n
    g.generic.coefficients g.generic.coefficientTransition g.coefficients g.transitions
    g.generic.push g.push_eq
    ⟨(g.generic.inverseImage n).modules, g.generic.levelPush n, g.generic.levelAdjunction n⟩
    (g.levelAdjunction_eq n) (g.generic.ordinaryPushEvaluation n)
    (g.ordinaryPushEvaluation_eq n) (g.generic.ordinaryPushEvaluation_sections n) N U x


private theorem pushComparison_sections (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : Geometry l E b f) (c : PushModel l E f (tau l E X) (tau l E Y))
    (d : g.push ≅ c.push)
    (hd : ∀ (M : S l E X) (n : ℕ), (ev l E Y n).map (d.hom.app M) =
      (pushLevelComparison l E b g c n).hom.app M)
    (M : S l E X) (V : (ℕ × Y.ProEt)ᵒᵖ) (x : (g.push.obj M).val.obj V) :
    HEq ((d.hom.app M).val.app V x) x := by
  have he : (ev l E Y V.unop.1).map (d.hom.app M) ≫
      (c.evaluation V.unop.1).hom.app M =
      (g.ordinaryPushEvaluation V.unop.1).hom.app M := by
    rw [hd]
    simp only [pushLevelComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hsec := c.sections M V.unop.1 (op V.unop.2) ((d.hom.app M).val.app V x)
  have hval := congrArg (fun k ↦ k.val.app (op V.unop.2) x) he
  exact hsec.symm.trans ((heq_of_eq hval).trans
    (pushEvaluationSections l E g V.unop.1 M (op V.unop.2) x))

private theorem inverse_sections {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} A} (d : M ≅ N)
    (hs : ∀ V (x : M.val.obj V), HEq (d.hom.val.app V x) x)
    (V : Cᵒᵖ) (y : N.val.obj V) : HEq (d.inv.val.app V y) y := by
  have hh := hs V (d.inv.val.app V y)
  have he : d.hom.val.app V (d.inv.val.app V y) = y :=
    congrArg (fun k : N ⟶ N ↦ k.val.app V y) d.inv_hom_id
  exact hh.symm.trans (heq_of_eq he)

end PushCoordinates

private theorem functorEq_sections {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    {D : Type*} [Category D] {F G : D ⥤ SheafOfModules.{u + 1} R}
    (p : F = G) (M : D) (V : Cᵒᵖ) (x : (F.obj M).val.obj V) :
    HEq (((eqToIso p).hom.app M).val.app V x) x := by
  subst G
  rfl

private theorem inverseMate_rightTransport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ Q₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ Q₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ Q₁) (d : R₂ ≅ Q₂)
    {G : A ⥤ C} {H : B ⥤ D} (q : R₁ ⋙ G ⟶ H ⋙ R₂) :
    ((mateEquiv (a.ofNatIsoRight e) (b.ofNatIsoRight d)).symm
      (Functor.whiskerRight e.inv G ≫ q ≫ Functor.whiskerLeft H d.hom)).natTrans =
      ((mateEquiv a b).symm q).natTrans := by
  ext M
  simp only [mateEquiv, Equiv.coe_fn_symm_mk, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Category.id_comp, Category.comp_id]

private theorem inverseMate_conjugation_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (q : R₁ ⋙ G ⟶ H ⋙ R₂) (e : G' ≅ G) (d : H ≅ H')
    [IsIso ((mateEquiv a b).symm q).natTrans] :
    IsIso ((mateEquiv a b).symm
      (Functor.whiskerLeft R₁ e.hom ≫ q ≫ Functor.whiskerRight d.hom R₂)).natTrans := by
  let v := (mateEquiv a b).symm q
  have hv : mateEquiv a b ((v.whiskerTop e.hom).whiskerBottom d.hom) =
      TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft R₁ e.hom ≫ q ≫ Functor.whiskerRight d.hom R₂) := by
    rw [mateEquiv_whiskerTop_whiskerBottom, Equiv.apply_symm_apply]
    ext X
    simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  change IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _
    (Functor.whiskerLeft R₁ e.hom ≫ q ≫ Functor.whiskerRight d.hom R₂))).natTrans
  rw [← hv, Equiv.symm_apply_apply]
  dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.mk]
  infer_instance

section ExactSquares

variable {A B C D : Type t} [Category.{v} A] [Category.{v} B]
  [Category.{v} C] [Category.{v} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]

private theorem exactSquare_rep (e : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
        I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
        I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  apply (cancel_epi (G.mapDerivedCategoryFactors.inv.app
    ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K))).mp
  have hh := CategoryTheory.square_fac e K
  have he :
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).inv.app K =
      (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K := by
    ext i
    simp only [Functor.comp_obj, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.refl_hom, NatTrans.id_app,
      NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
      Iso.refl_inv]
    erw [Category.id_comp, Category.comp_id]
  rw [he] at hh
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact hh

private def conjugatedSquare (e : F ⋙ G ≅ H ⋙ I)
    {S : DerivedCategory A ⥤ DerivedCategory B}
    {T : DerivedCategory C ⥤ DerivedCategory D}
    (k : S ≅ F.mapDerivedCategory) (l : T ≅ I.mapDerivedCategory) :
    S ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory ⋙ T :=
  Functor.isoWhiskerRight k G.mapDerivedCategory ≪≫
    Functor.mapDerivedCategorySquareIso e ≪≫
    Functor.isoWhiskerLeft H.mapDerivedCategory l.symm

private theorem conjugatedSquare_rep (e : F ⋙ G ≅ H ⋙ I)
    {S : DerivedCategory A ⥤ DerivedCategory B}
    {T : DerivedCategory C ⥤ DerivedCategory D}
    (k : S ≅ F.mapDerivedCategory) (l : T ≅ I.mapDerivedCategory)
    (εS : DerivedCategory.Q ⋙ S ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εT : DerivedCategory.Q ⋙ T ⟶ I.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hk : ∀ K, k.hom.app (DerivedCategory.Q.obj K) ≫
      F.mapDerivedCategoryFactors.hom.app K = εS.app K)
    (hl : ∀ K, l.hom.app (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategoryFactors.hom.app K = εT.app K)
    (K : CochainComplex A ℤ) :
    (conjugatedSquare F G H I e k l).hom.app (DerivedCategory.Q.obj K) ≫
        T.map (H.mapDerivedCategoryFactors.hom.app K) ≫
        εT.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
      G.mapDerivedCategory.map (εS.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  simp only [conjugatedSquare, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← hl]
  rw [reassoc_of% (l.hom.naturality (H.mapDerivedCategoryFactors.hom.app K))]
  simp only [Iso.inv_hom_id_app_assoc]
  have hh := congrArg (fun z ↦
    G.mapDerivedCategory.map (k.hom.app (DerivedCategory.Q.obj K)) ≫ z)
      (exactSquare_rep F G H I e K)
  simpa only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, ← hk K, Functor.map_comp, Category.assoc] using hh

end ExactSquares

section CoefficientSquare

variable (P : PurityFiniteSetting.{u}) {E F : Index P} {h : E ≤ F}
  (a : Coefficients P E F h)

private def liftedCoefficient (n : ℕ) :
    SpTowerShriek.VR P.coefficients.l E.val n ⟶
      SpTowerShriek.VR P.coefficients.l F.val n :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((a.quotient n).comp ULift.ringEquiv.toRingHom))

private theorem coefficientMap_sections (T : Scheme.{u}) (V : (ℕ × T.ProEt)ᵒᵖ) :
    (coefficientMap P a T).hom.app V =
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (liftedCoefficient P a V.unop.1)).hom.app (op V.unop.2) := by
  unfold coefficientMap SemilinearSections.systemMap
  rw [(systemMap_existsUnique (ProEt.topology T)
    (SpTowerShriek.B P.coefficients.l E.val T) (SpTowerShriek.tau P.coefficients.l E.val T)
    (SpTowerShriek.B P.coefficients.l F.val T) (SpTowerShriek.tau P.coefficients.l F.val T)
    (fun n ↦ (a.tower T).app (op n))
    (fun n ↦ ((a.tower T).naturality (homOfLE (Nat.le_succ n)).op).symm)).exists.choose_spec
      V.unop.1 (op V.unop.2)]
  rw [a.tower_app]
  rfl

private theorem coefficientPush_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cE : PushModel P.coefficients.l E.val f
      (SpTowerShriek.tau P.coefficients.l E.val X)
      (SpTowerShriek.tau P.coefficients.l E.val Y))
    (cF : PushModel P.coefficients.l F.val f
      (SpTowerShriek.tau P.coefficients.l F.val X)
      (SpTowerShriek.tau P.coefficients.l F.val Y)) :
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientMap P a Y)) ≫
        cF.ringMap =
      cE.ringMap ≫ ((VaryingRing.baseChange f).sheafPushforwardContinuous
        RingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).map
          ((sheafCompose (coefficientSequenceTopology (ProEt.topology X))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientMap P a X)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((coefficientMap P a Y).hom.app V) ≫ cF.ringMap.hom.app V =
    cE.ringMap.hom.app V ≫ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((coefficientMap P a X).hom.app ((VaryingRing.baseChange f).op.obj V))
  rw [coefficientMap_sections, coefficientMap_sections, cE.ringMap_app, cF.ringMap_app]
  exact congrArg (fun q ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    (q.hom.app (op V.unop.2)))
      (VaryingRing.constantMap_naturality f (liftedCoefficient P a V.unop.1))

private theorem canonicalRestrictionPush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cE : PushModel P.coefficients.l E.val f
      (SpTowerShriek.tau P.coefficients.l E.val X)
      (SpTowerShriek.tau P.coefficients.l E.val Y))
    (cF : PushModel P.coefficients.l F.val f
      (SpTowerShriek.tau P.coefficients.l F.val X)
      (SpTowerShriek.tau P.coefficients.l F.val Y)) :
    ∃ d : cF.push ⋙ res (coefficientMap P a Y) ≅
        res (coefficientMap P a X) ⋙ cE.push,
      ∀ (N : SpTowerShriek.S P.coefficients.l F.val X) (V : (ℕ × Y.ProEt)ᵒᵖ)
        (x : ((cF.push ⋙ res (coefficientMap P a Y)).obj N).val.obj V),
        HEq ((d.hom.app N).val.app V x) x := by
  rw [cE.push_eq, cF.push_eq]
  obtain ⟨d, hd⟩ := restriction_pushforward_square (VaryingRing.baseChange f)
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientMap P a Y))
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology X))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientMap P a X))
    cE.ringMap cF.ringMap (coefficientPush_square P a f cE cF)
  refine ⟨d, ?_⟩
  intro N V x
  exact heq_of_eq (congrFun (eq_of_heq (hd N V.unop)) x)

private theorem restrictionPush_exists
    (bE : SpTowerShriek.Base P.coefficients.l E.val)
    (bF : SpTowerShriek.Base P.coefficients.l F.val)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gE : SpTowerShriek.Geometry P.coefficients.l E.val bE f)
    (gF : SpTowerShriek.Geometry P.coefficients.l F.val bF f) :
    ∃ d : res (coefficientMap P a X) ⋙ gE.push ≅
        gF.push ⋙ res (coefficientMap P a Y),
      ∀ (M : SpTowerShriek.S P.coefficients.l F.val X) (V : (ℕ × Y.ProEt)ᵒᵖ)
        (x : ((res (coefficientMap P a X) ⋙ gE.push).obj M).val.obj V),
        HEq ((d.hom.app M).val.app V x) x := by
  obtain ⟨cE⟩ := canonicalPushModel P.coefficients.l E.val f _ _
    (SpTowerShriek.tau_eq _ _ X) (SpTowerShriek.tau_eq _ _ Y)
  obtain ⟨cF⟩ := canonicalPushModel P.coefficients.l F.val f _ _
    (SpTowerShriek.tau_eq _ _ X) (SpTowerShriek.tau_eq _ _ Y)
  obtain ⟨dE, hdE⟩ := pushComparison_exists P.coefficients.l E.val bE gE cE
  obtain ⟨dF, hdF⟩ := pushComparison_exists P.coefficients.l F.val bF gF cF
  obtain ⟨c, hc⟩ := canonicalRestrictionPush P a f cE cF
  let d := Functor.isoWhiskerLeft (res (coefficientMap P a X)) dE ≪≫ c.symm ≪≫
    Functor.isoWhiskerRight dF.symm (res (coefficientMap P a Y))
  refine ⟨d, ?_⟩
  intro M V x
  have hE := pushComparison_sections P.coefficients.l E.val bE gE cE dE hdE
    ((res (coefficientMap P a X)).obj M) V x
  have hC := inverse_sections (c.app M) (hc M) V
    ((dE.hom.app ((res (coefficientMap P a X)).obj M)).val.app V x)
  have hF := inverse_sections (dF.app M)
    (pushComparison_sections P.coefficients.l F.val bF gF cF dF hdF M) V
    ((c.inv.app M).val.app V
      ((dE.hom.app ((res (coefficientMap P a X)).obj M)).val.app V x))
  exact hF.trans (hC.trans hE)

private theorem quotientFreeFinite
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Free R S] [Module.Finite R S]
    (x : R) (y : S) (hxy : algebraMap R S x = y)
    (I : Ideal R) (J : Ideal S) (hI : I = Ideal.span {x}) (hJ : J = Ideal.span {y})
    (q : (R ⧸ I) →+* (S ⧸ J))
    (hq : ∀ r, q (Ideal.Quotient.mk I r) = Ideal.Quotient.mk J (algebraMap R S r)) :
    @Module.Free _ _ _ _ q.toAlgebra.toModule ∧
      @Module.Finite _ _ _ _ q.toAlgebra.toModule := by
  subst I J
  obtain ⟨q', hq', hf, hfin⟩ := Padic.quotient_free_finite x y hxy
  have he : q' = q := by
    ext r
    exact (hq' r).trans (hq r).symm
  subst q'
  exact ⟨hf, hfin⟩

private theorem quotientCoefficient_free (n : ℕ) :
    @Module.Free _ _ _ _ (a.quotient n).toAlgebra.toModule ∧
      @Module.Finite _ _ _ _ (a.quotient n).toAlgebra.toModule := by
  let ι := IntermediateField.inclusion h
  let := ι.toAlgebra
  let := (integralScalarIntegerInclusion P.coefficients.l E.val F.val ι).toAlgebra
  obtain ⟨b⟩ := WeilConjectures.integral_basis P.coefficients.l E.val F.val ι
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  apply quotientFreeFinite
    ((P.coefficients.l : Padic.coefficientExtensionIntegers P.coefficients.l E.val) ^ (n + 1))
    ((P.coefficients.l : Padic.coefficientExtensionIntegers P.coefficients.l F.val) ^ (n + 1))
    (by simp) _ _
    (by exact Ideal.span_singleton_pow _ _) (by exact Ideal.span_singleton_pow _ _)
    (a.quotient n) (a.quotient_mk n)

private theorem liftedCoefficient_free (n : ℕ) :
    @Module.Free _ _ _ _ (liftedCoefficient P a n).hom.toAlgebra.toModule ∧
      @Module.Finite _ _ _ _ (liftedCoefficient P a n).hom.toAlgebra.toModule := by
  let := (a.quotient n).toAlgebra
  let := (liftedCoefficient P a n).hom.toAlgebra
  have hf := quotientCoefficient_free P a n
  have := hf.1
  have := hf.2
  let σ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.VR P.coefficients.l E.val n := ULift.ringEquiv.symm.toRingHom
  have : RingHomInvPair σ ULift.ringEquiv.toRingHom :=
    ⟨rfl, by ext x; cases x; rfl⟩
  have : RingHomInvPair ULift.ringEquiv.toRingHom σ :=
    ⟨by ext x; cases x; rfl, rfl⟩
  let d : SpTowerShriek.R P.coefficients.l F.val n ≃ₛₗ[σ]
      SpTowerShriek.VR P.coefficients.l F.val n :=
    { toAddEquiv := ULift.ringEquiv.symm.toAddEquiv
      map_smul' := fun _ _ ↦ rfl }
  exact ⟨Module.Free.of_equiv (σ' := ULift.ringEquiv.toRingHom) d,
    Module.Finite.of_surjective d.toLinearMap d.surjective⟩

private theorem scalar_exact (T : Scheme.{u}) (s : Scalars P a T) :
    PreservesFiniteLimits s.model.E ∧ PreservesFiniteColimits s.model.E := by
  have hf (V : (ℕ × T.ProEt)ᵒᵖ) : ((coefficientMap P a T).hom.app V).hom.Flat := by
    rw [coefficientMap_sections]
    let n := V.unop.1
    let := (liftedCoefficient P a n).hom.toAlgebra
    have hfree := liftedCoefficient_free P a n
    have := hfree.1
    have := hfree.2
    obtain ⟨q, β, _⟩ := @constantFiniteFree_sectionBasis.{u + 1, u, u + 1}
      T.ProEt inferInstance (ProEt.topology T)
      (inferInstance : HasSheafify (ProEt.topology T) CommRingCat.{u + 1})
      (inferInstance : (ProEt.topology T).HasSheafCompose
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (inferInstance : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1})
      (locallyBijective.{u + 1, u, u + 1} (ProEt.topology T))
      (SpTowerShriek.VR P.coefficients.l E.val n)
      (SpTowerShriek.VR P.coefficients.l F.val n) inferInstance inferInstance inferInstance
    let := (((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (liftedCoefficient P a n)).hom.app (op V.unop.2)).hom.toAlgebra
    let : Module.Free
        ((SpTowerShriek.B P.coefficients.l E.val T n).obj.obj (op V.unop.2))
        ((SpTowerShriek.B P.coefficients.l F.val T n).obj.obj (op V.unop.2)) :=
      Module.Free.of_basis (β (op V.unop.2))
    exact inferInstanceAs (Module.Flat
      ((SpTowerShriek.B P.coefficients.l E.val T n).obj.obj (op V.unop.2))
      ((SpTowerShriek.B P.coefficients.l F.val T n).obj.obj (op V.unop.2)))
  have hl := scalarModel_limits_of_flat (coefficientMap P a T) s.model hf
  have := s.ordinaryAdjunction.isLeftAdjoint
  exact ⟨hl, inferInstance⟩

private theorem scalar_counit_iso (T : Scheme.{u}) (s : Scalars P a T)
    [PreservesFiniteLimits s.model.E] [PreservesFiniteColimits s.model.E] :
    IsIso s.model.ε := by
  have hh := (s.model.E.exactFunctor_derivedFunctor s.model.E.mapDerivedCategory
    s.model.E.mapDerivedCategoryFactors).2.2.2.1 s.T s.model.ε s.model.universal
  have (K : CochainComplex (SpTowerShriek.S P.coefficients.l E.val T) ℤ) :
      IsIso (s.model.ε.app K) := hh K
  exact NatIso.isIso_of_isIso_app _

private theorem exactScalarComparison (T : Scheme.{u}) (s : Scalars P a T)
    [PreservesFiniteLimits s.model.E] [PreservesFiniteColimits s.model.E] :
    ∃ k : s.T ≅ s.model.E.mapDerivedCategory,
      ∀ K, k.hom.app (DerivedCategory.Q.obj K) ≫
        s.model.E.mapDerivedCategoryFactors.hom.app K = s.model.ε.app K := by
  have := scalar_counit_iso P a T s
  let W := HomologicalComplex.quasiIso (SpTowerShriek.S P.coefficients.l E.val T) (.up ℤ)
  let : Localization.Lifting DerivedCategory.Q W (DerivedCategory.Q ⋙ s.T) s.T :=
    ⟨Iso.refl _⟩
  let : Localization.Lifting DerivedCategory.Q W
      (s.model.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      s.model.E.mapDerivedCategory := ⟨s.model.E.mapDerivedCategoryFactors⟩
  let k := Localization.liftNatIso DerivedCategory.Q W _ _ s.T
    s.model.E.mapDerivedCategory (asIso s.model.ε)
  refine ⟨k, ?_⟩
  intro K
  simp only [k, Localization.liftNatIso_hom]
  rw [Localization.liftNatTrans_app]
  change (𝟙 _ ≫ s.model.ε.app K ≫ s.model.E.mapDerivedCategoryFactors.inv.app K) ≫
    s.model.E.mapDerivedCategoryFactors.hom.app K = s.model.ε.app K
  simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]


private def ordinaryComparison
    (bE : SpTowerShriek.Base P.coefficients.l E.val)
    (bF : SpTowerShriek.Base P.coefficients.l F.val)
    (s : ∀ T, Scalars P a T)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (gE : SpTowerShriek.Geometry P.coefficients.l E.val bE f)
    (gF : SpTowerShriek.Geometry P.coefficients.l F.val bF f)
    (d : res (coefficientMap P a X) ⋙ gE.push ≅
      gF.push ⋙ res (coefficientMap P a Y)) :
    (s Y).model.E ⋙ gF.pull ≅ gE.pull ⋙ (s X).model.E :=
  ((conjugateIsoEquiv ((s Y).ordinaryAdjunction.comp gF.ordinaryAdjunction)
    (gE.ordinaryAdjunction.comp (s X).ordinaryAdjunction)).symm d.symm).symm

private theorem ordinaryComparison_mate
    (bE : SpTowerShriek.Base P.coefficients.l E.val)
    (bF : SpTowerShriek.Base P.coefficients.l F.val)
    (s : ∀ T, Scalars P a T)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (gE : SpTowerShriek.Geometry P.coefficients.l E.val bE f)
    (gF : SpTowerShriek.Geometry P.coefficients.l F.val bF f)
    (d : res (coefficientMap P a X) ⋙ gE.push ≅
      gF.push ⋙ res (coefficientMap P a Y)) :
    (mateEquiv (s Y).ordinaryAdjunction (s X).ordinaryAdjunction
      (ordinaryComparison P a bE bF s gE gF d).inv).natTrans =
      ((mateEquiv gF.ordinaryAdjunction gE.ordinaryAdjunction).symm d.inv).natTrans := by
  have hc : conjugateEquiv ((s Y).ordinaryAdjunction.comp gF.ordinaryAdjunction)
      (gE.ordinaryAdjunction.comp (s X).ordinaryAdjunction)
      (ordinaryComparison P a bE bF s gE gF d).inv = d.inv := by
    exact congrArg Iso.hom ((conjugateIsoEquiv
      ((s Y).ordinaryAdjunction.comp gF.ordinaryAdjunction)
      (gE.ordinaryAdjunction.comp (s X).ordinaryAdjunction)).apply_symm_apply d.symm)
  rw [← iterated_mateEquiv_conjugateEquiv] at hc
  exact congrArg TwoSquare.natTrans
    ((mateEquiv gF.ordinaryAdjunction gE.ordinaryAdjunction).injective
      (by simpa only [Equiv.apply_symm_apply] using hc))

private theorem restrictionPull_open_iso
    (bE : SpTowerShriek.Base P.coefficients.l E.val)
    (bF : SpTowerShriek.Base P.coefficients.l F.val)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (gE : SpTowerShriek.Geometry P.coefficients.l E.val bE j)
    (gF : SpTowerShriek.Geometry P.coefficients.l F.val bF j)
    (d : res (coefficientMap P a X) ⋙ gE.push ≅ gF.push ⋙ res (coefficientMap P a Y))
    (hd : ∀ M V (x : ((res (coefficientMap P a X) ⋙ gE.push).obj M).val.obj V),
      HEq ((d.hom.app M).val.app V x) x) :
    IsIso ((mateEquiv gF.ordinaryAdjunction gE.ordinaryAdjunction).symm d.inv).natTrans := by
  obtain ⟨cE⟩ := canonicalPushModel P.coefficients.l E.val j _ _
    (SpTowerShriek.tau_eq _ _ X) (SpTowerShriek.tau_eq _ _ Y)
  obtain ⟨cF⟩ := canonicalPushModel P.coefficients.l F.val j _ _
    (SpTowerShriek.tau_eq _ _ X) (SpTowerShriek.tau_eq _ _ Y)
  obtain ⟨dE, hdE⟩ := pushComparison_exists P.coefficients.l E.val bE gE cE
  obtain ⟨dF, hdF⟩ := pushComparison_exists P.coefficients.l F.val bF gF cF
  let eE := dE ≪≫ eqToIso cE.push_eq
  let eF := dF ≪≫ eqToIso cF.push_eq
  have heE (M : SpTowerShriek.S P.coefficients.l E.val X) V
      (x : (gE.push.obj M).val.obj V) : HEq ((eE.hom.app M).val.app V x) x :=
    (functorEq_sections cE.push_eq M V ((dE.hom.app M).val.app V x)).trans
      (pushComparison_sections P.coefficients.l E.val bE gE cE dE hdE M V x)
  have heF (M : SpTowerShriek.S P.coefficients.l F.val X) V
      (x : (gF.push.obj M).val.obj V) : HEq ((eF.hom.app M).val.app V x) x :=
    (functorEq_sections cF.push_eq M V ((dF.hom.app M).val.app V x)).trans
      (pushComparison_sections P.coefficients.l F.val bF gF cF dF hdF M V x)
  let aY := (sheafCompose (coefficientSequenceTopology (ProEt.topology Y))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientMap P a Y)
  let aX := (sheafCompose (coefficientSequenceTopology (ProEt.topology X))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientMap P a X)
  obtain ⟨q, hq⟩ := restriction_pushforward_square (VaryingRing.baseChange j)
    aY aX cE.ringMap cF.ringMap (coefficientPush_square P a j cE cF)
  let := VaryingRing.prodOpenContinuous j
  let := cE.openTranspose
  let := cF.openTranspose
  let s := VaryingRing.prodAdj (VaryingRing.openAdj j)
  let ae := VaryingRing.moduleAdjOfSiteAdj
    (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceTopology (ProEt.topology Y)) s cE.ringMap
  let af := VaryingRing.moduleAdjOfSiteAdj
    (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceTopology (ProEt.topology Y)) s cF.ringMap
  have hraw := ringed_inverse_mate_iso s aY aX cE.ringMap cF.ringMap
    (coefficientPush_square P a j cE cF) q hq
  let v := Functor.isoWhiskerRight eF (res (coefficientMap P a Y)) ≪≫ q ≪≫
    Functor.isoWhiskerLeft (res (coefficientMap P a X)) eE.symm
  have hv : d.inv = v.hom := by
    ext M V x
    have hd' := inverse_sections (d.app M) (hd M) V x
    have h1 := heF M V x
    have h2 := congrFun (eq_of_heq (hq M V.unop)) ((eF.hom.app M).val.app V x)
    have h3 := inverse_sections (eE.app ((res (coefficientMap P a X)).obj M))
      (heE ((res (coefficientMap P a X)).obj M)) V
      ((q.hom.app M).val.app V ((eF.hom.app M).val.app V x))
    exact eq_of_heq (hd'.trans (h3.trans ((heq_of_eq h2).trans h1)).symm)
  rw [hv]
  have hi : IsIso ((mateEquiv (af.ofNatIsoRight eF.symm)
      (ae.ofNatIsoRight eE.symm)).symm v.hom).natTrans := by
    change IsIso ((mateEquiv (af.ofNatIsoRight eF.symm)
      (ae.ofNatIsoRight eE.symm)).symm
      (Functor.whiskerRight eF.hom (res (coefficientMap P a Y)) ≫ q.hom ≫
        Functor.whiskerLeft (res (coefficientMap P a X)) eE.inv)).natTrans
    exact (inverseMate_rightTransport af ae eF.symm eE.symm q.hom).symm ▸ hraw
  exact AlgebraicGeometry.ProEtale.SemilinearProperOpen.inverse_mate_change_isIso
    gF.ordinaryAdjunction (af.ofNatIsoRight eF.symm)
    gE.ordinaryAdjunction (ae.ofNatIsoRight eE.symm) v.hom

private theorem ordinaryOpenMate_iso
    (bE : SpTowerShriek.Base P.coefficients.l E.val)
    (bF : SpTowerShriek.Base P.coefficients.l F.val)
    (oE : SpTowerShriek.Operations P.coefficients.l E.val bE)
    (oF : SpTowerShriek.Operations P.coefficients.l F.val bF)
    (s : ∀ T, Scalars P a T) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (c : PullComparison P a bE bF oE oF s j) :
    IsIso ((mateEquiv (oE.openOp j).ordinaryAdjunction
      (oF.openOp j).ordinaryAdjunction).symm c.ordinary.inv).natTrans := by
  have := restrictionPull_open_iso P a bE bF j (oE.geometry j) (oF.geometry j)
    c.restrictionPush c.sections
  have he : c.ordinary.inv =
      ((mateEquiv (s Y).ordinaryAdjunction (s X).ordinaryAdjunction).symm
        ((mateEquiv (oF.geometry j).ordinaryAdjunction
          (oE.geometry j).ordinaryAdjunction).symm c.restrictionPush.inv)).natTrans := by
    apply congrArg TwoSquare.natTrans
    apply (mateEquiv (s Y).ordinaryAdjunction (s X).ordinaryAdjunction).injective
    rw [Equiv.apply_symm_apply]
    exact congrArg (TwoSquare.mk _ _ _ _) c.ordinary_mate
  rw [he, iterated_mateEquiv_conjugateEquiv_symm]
  change IsIso ((conjugateEquiv
    ((oE.openOp j).ordinaryAdjunction.comp (s Y).ordinaryAdjunction)
    ((s X).ordinaryAdjunction.comp (oF.openOp j).ordinaryAdjunction)).symm
    ((mateEquiv (oF.geometry j).ordinaryAdjunction
      (oE.geometry j).ordinaryAdjunction).symm c.restrictionPush.inv).natTrans)
  infer_instance

private theorem pullComparison_exists
    (bE : SpTowerShriek.Base P.coefficients.l E.val)
    (bF : SpTowerShriek.Base P.coefficients.l F.val)
    (oE : SpTowerShriek.Operations P.coefficients.l E.val bE)
    (oF : SpTowerShriek.Operations P.coefficients.l F.val bF)
    (s : ∀ T, Scalars P a T) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (PullComparison P a bE bF oE oF s f) := by
  obtain ⟨d, hd⟩ := restrictionPush_exists P a bE bF f (oE.geometry f) (oF.geometry f)
  have hX := scalar_exact P a X (s X)
  have hY := scalar_exact P a Y (s Y)
  have := hX.1
  have := hX.2
  have := hY.1
  have := hY.2
  obtain ⟨k, hk⟩ := exactScalarComparison P a Y (s Y)
  obtain ⟨l, hl⟩ := exactScalarComparison P a X (s X)
  let e := ordinaryComparison P a bE bF s (oE.geometry f) (oF.geometry f) d
  refine ⟨{
    restrictionPush := d
    sections := hd
    ordinary := e
    ordinary_mate := ordinaryComparison_mate P a bE bF s (oE.geometry f) (oF.geometry f) d
    derived := conjugatedSquare _ _ _ _ e k l
    representative := ?_ }⟩
  intro K _
  exact conjugatedSquare_rep _ _ _ _ e k l (s Y).model.ε (s X).model.ε hk hl K

set_option maxHeartbeats 3200000 in
-- Resolution descent and the two adjunction transports involve large coefficient models.
private theorem derivedOpenMate_iso
    (bE : SpTowerShriek.Base P.coefficients.l E.val)
    (bF : SpTowerShriek.Base P.coefficients.l F.val)
    (oE : SpTowerShriek.Operations P.coefficients.l E.val bE)
    (oF : SpTowerShriek.Operations P.coefficients.l F.val bF)
    (s : ∀ T, Scalars P a T) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (c : PullComparison P a bE bF oE oF s j) :
    IsIso ((mateEquiv (oE.openOp j).derivedAdjunction
      (oF.openOp j).derivedAdjunction).symm c.derived.inv).natTrans := by
  have hX := scalar_exact P a X (s X)
  have hY := scalar_exact P a Y (s Y)
  have := hX.1
  have := hX.2
  have := hY.1
  have := hY.2
  have := scalar_counit_iso P a X (s X)
  obtain ⟨k, hk⟩ := exactScalarComparison P a Y (s Y)
  obtain ⟨l, hl⟩ := exactScalarComparison P a X (s X)
  let e := conjugatedSquare (s Y).model.E (oF.geometry j).pull
    (oE.geometry j).pull (s X).model.E c.ordinary k l
  have he : c.derived = e := by
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (SpTowerShriek.S P.coefficients.l E.val Y) (.up ℤ))
    intro K
    obtain ⟨L, q, hL, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := systemRing (ProEt.topology Y) (SpTowerShriek.B P.coefficients.l E.val Y)
          (SpTowerShriek.tau P.coefficients.l E.val Y)) K
    have : QuasiIso q := hq
    have hr : c.derived.hom.app (DerivedCategory.Q.obj L) =
        e.hom.app (DerivedCategory.Q.obj L) := by
      have hε := NatIso.isIso_app_of_isIso (s X).model.ε
        (((oE.geometry j).pull.mapHomologicalComplex (.up ℤ)).obj L)
      have hm := CategoryTheory.Functor.map_isIso (s X).T
        ((oE.geometry j).pull.mapDerivedCategoryFactors.hom.app L)
      have := IsIso.comp_isIso' hm hε
      have : Mono ((s X).T.map
          ((oE.geometry j).pull.mapDerivedCategoryFactors.hom.app L) ≫
            (s X).model.ε.app (((oE.geometry j).pull.mapHomologicalComplex (.up ℤ)).obj L)) :=
        IsIso.mono_of_iso _
      apply (cancel_mono ((s X).T.map
        ((oE.geometry j).pull.mapDerivedCategoryFactors.hom.app L) ≫
          (s X).model.ε.app (((oE.geometry j).pull.mapHomologicalComplex (.up ℤ)).obj L))).mp
      have h1 := c.representative L hL
      have h2 := conjugatedSquare_rep (s Y).model.E (oF.geometry j).pull
        (oE.geometry j).pull (s X).model.E c.ordinary k l
        (s Y).model.ε (s X).model.ε hk hl L
      exact h1.trans h2.symm
    have : IsIso (DerivedCategory.Q.map q) := inferInstance
    have := CategoryTheory.Functor.map_isIso
      ((s Y).T ⋙ (oF.geometry j).pull.mapDerivedCategory) (DerivedCategory.Q.map q)
    have : Epi (((s Y).T ⋙ (oF.geometry j).pull.mapDerivedCategory).map
        (DerivedCategory.Q.map q)) := IsIso.epi_of_iso _
    apply (cancel_epi (((s Y).T ⋙ (oF.geometry j).pull.mapDerivedCategory).map
      (DerivedCategory.Q.map q))).mp
    rw [c.derived.hom.naturality, e.hom.naturality, hr]
  rw [he]
  have : IsIso ((mateEquiv (oE.openOp j).ordinaryAdjunction
      (oF.openOp j).ordinaryAdjunction).symm
      (TwoSquare.mk (oE.geometry j).pull (s Y).model.E (s X).model.E
        (oF.geometry j).pull c.ordinary.symm.hom)).natTrans := by
    simpa only [Iso.symm_hom] using ordinaryOpenMate_iso P a bE bF oE oF s j c
  have hi := CategoryTheory.exact_localization_inverse_mate
    (oE.openOp j).ordinaryAdjunction (oF.openOp j).ordinaryAdjunction c.ordinary.symm
  have := hi.1
  have hconj := inverseMate_conjugation_iso
    (CategoryTheory.exactLocalizationDerivedAdjunction (oE.openOp j).ordinaryAdjunction)
    (CategoryTheory.exactLocalizationDerivedAdjunction (oF.openOp j).ordinaryAdjunction)
    (Functor.mapDerivedCategorySquareIso c.ordinary.symm).hom l k.symm
  have : IsIso ((mateEquiv
      (CategoryTheory.exactLocalizationDerivedAdjunction (oE.openOp j).ordinaryAdjunction)
      (CategoryTheory.exactLocalizationDerivedAdjunction (oF.openOp j).ordinaryAdjunction)).symm
      e.inv).natTrans := by
    simpa only [e, conjugatedSquare, Iso.trans_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_inv, Iso.symm_inv, Iso.symm_hom,
      Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.trans_inv, Category.assoc] using hconj
  exact AlgebraicGeometry.ProEtale.SemilinearProperOpen.inverse_mate_change_isIso
    (oE.openOp j).derivedAdjunction
    (CategoryTheory.exactLocalizationDerivedAdjunction (oE.openOp j).ordinaryAdjunction)
    (oF.openOp j).derivedAdjunction
    (CategoryTheory.exactLocalizationDerivedAdjunction (oF.openOp j).ordinaryAdjunction) e.inv

end CoefficientSquare

/-- For prescribed bases, geometric operations, actual coefficient maps and normalized
scalar extensions, the scalar/pullback comparison and open tensor mate exist.

Source: latest blueprint, field-extension towers proof (2), simultaneous models
and open tensor identification
(blueprint: lem-route-field-shriek-system-geometry).

Proof:
1. Assemble the prescribed finite pushforward coordinates into a comparison with
   the continuous pushforward on the ringed sequence site. The ordinary horizontal
   unit normalization makes these coordinates commute with every coefficient
   transition. Both coordinate maps preserve every section.
2. Constant coefficient maps commute with geometric ring maps. Thus scalar
   restriction and continuous pushforward commute by the identity on sections.
   Transport this square to the prescribed pushforwards. Conjugation of the two
   composite adjunctions gives the ordinary scalar/pullback comparison and its
   double-mate normalization.
3. An integral basis for O_F over O_E descends to a finite free basis modulo each
   positive power of ell. Lift the coefficient rings to the site universe and use
   the constant finite-free section-basis theorem. The actual coefficient map is
   flat on every section of the sequence site. Hence ordinary scalar extension
   is exact, and its universal derived counit is invertible on every complex.
4. Identify each supplied derived scalar functor with localization of its ordinary
   model using that counit. Localize the ordinary square and conjugate by these
   identifications. The standard localization factors give representative exactly.
5. For an open immersion the geometric ring maps have invertible transposes under
   the open-site adjunction. The section-identity restriction square therefore has
   an invertible inverse mate. Transport to the prescribed ordinary adjunctions;
   the iterated-mate identity gives invertibility of the ordinary open scalar mate.
   Exact localization preserves this property. The representative equation
   identifies the prescribed derived comparison with the localized square on
   K-flat resolutions, hence everywhere. Conjugation and change of adjunction
   preserve mate invertibility. Take the inverse of this invertible mate as openIso;
   open_unit then holds by construction. -/
theorem field_shriek_geometry_exists (P : PurityFiniteSetting.{u})
    (base : ∀ E : Index P, SpTowerShriek.Base P.coefficients.l E.val)
    (operations : ∀ E : Index P, SpTowerShriek.Operations P.coefficients.l E.val (base E))
    (coefficients : ∀ (E F : Index P) (h : E ≤ F), Coefficients P E F h)
    (scalars : ∀ (E F : Index P) (h : E ≤ F) (T : Scheme.{u}),
    Scalars P (coefficients E F h) T) :
    ∃ (pull : ∀ (E F : Index P) (h : E ≤ F) {X Y : Scheme.{u}} (f : X ⟶ Y),
    PullComparison P (coefficients E F h) (base E) (base F)
      (operations E) (operations F) (scalars E F h) f)
      (openIso : ∀ (E F : Index P) (h : E ≤ F) {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j],
    SpTowerShriek.openD P.coefficients.l E.val (base E) ((operations E).openOp j) ⋙
        (scalars E F h Z).T ≅
      (scalars E F h X).T ⋙
        SpTowerShriek.openD P.coefficients.l F.val (base F) ((operations F).openOp j)),
    ∀ (E F : Index P) (h : E ≤ F) {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j],
    (openIso E F h j).inv =
      ((mateEquiv ((operations E).openOp j).derivedAdjunction
        ((operations F).openOp j).derivedAdjunction).symm
          (pull E F h j).derived.inv).natTrans := by
  classical
  let pull (E F : Index P) (h : E ≤ F) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
    Classical.choice (pullComparison_exists P (coefficients E F h)
      (base E) (base F) (operations E) (operations F) (scalars E F h) f)
  have hi (E F : Index P) (h : E ≤ F) {X Y : Scheme.{u}}
      (j : X ⟶ Y) [IsOpenImmersion j] :=
    derivedOpenMate_iso P (coefficients E F h) (base E) (base F)
      (operations E) (operations F) (scalars E F h) j (pull E F h j)
  refine ⟨pull, fun E F h X Y j _ ↦
    (@asIso _ _ _ _ _ (hi E F h j)).symm, ?_⟩
  intros
  rfl

end AlgebraicGeometry.ProEtale.FieldShriekSystem
