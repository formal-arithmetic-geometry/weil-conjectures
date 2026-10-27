/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel
public import Sheaf.AlgebraicGeometry.AffineComponentSiteProjection
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Sheaf.AlgebraicGeometry.CondensedComponentInverseImage
import Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility
import Sheaf.Paper.RelativeComponentLiftPullbackSpace
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Unbounded evaluation of component pullback

Source: Hemo--Richarz--Scholbach, Section 3 and Proposition 4.3(1), equation (4.2)
(blueprint: lem-sfb-component-pullback-unbounded-evaluation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open CategoryTheory.MonoidalCategory

attribute [local instance] Sheaf.monoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Scalar restriction preserves finite limits in the fixed section-module universe.
Source: HRS Section 3, coefficient transport
(blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
instance componentScalarRestrictionLimits (R S : CommRingCat.{u + 1}) (f : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} f) := by
  let : (ModuleCat.restrictScalars.{u + 1} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1} f).isRightAdjoint
  infer_instance

/-- Scalar restriction preserves finite colimits in the fixed section-module universe.
Source: HRS Section 3, coefficient transport
(blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
instance componentScalarRestrictionColimits (R S : CommRingCat.{u + 1}) (f : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} f) := by
  let : (ModuleCat.restrictScalars.{u + 1} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, u + 1, u + 1} f).isLeftAdjoint
  infer_instance

/-- The component object of an affine pro-etale test, using the recorded qcqs construction.
Source: HRS Proposition 4.3(1), before (4.2)
(blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
abbrev componentAffineObject (W : Scheme.{u}) [IsAffine W]
    (U : W.ProEt) [IsAffine U.left] : Over (affineComponentSpace W) :=
  Scheme.ProEt.componentObject W ⟨U, inferInstance, inferInstance⟩

/-- The induced component map of affine tests, with its actual quotient topology.
Source: HRS Proposition 4.3(1), before (4.2)
(blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
abbrev componentAffineObjectMap {W : Scheme.{u}} [IsAffine W]
    {U V : W.ProEt} [IsAffine U.left] [IsAffine V.left] (f : U ⟶ V) :
    componentAffineObject W U ⟶ componentAffineObject W V :=
  Scheme.ProEt.componentObjectMap ⟨f⟩

/-- Projection of the uniquely characterized relative component test onto its profinite input.
Source: HRS (4.1), using the relative universal property
(blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
def componentTestProjection (W : Scheme.{u}) [IsAffine W] :
    ∀ E : Over (affineComponentSpace W), C(((componentTests W).obj E).left, E.left) :=
  Classical.choose ((Classical.choose_spec (component_relative_profinite_site W)).2.1)

/-- Actual module evaluation on the profinite component object.
Source: HRS (4.2) (blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
abbrev componentSourceSections (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (W : Scheme.{u}) [IsAffine W] (U : W.ProEt) [IsAffine U.left] :=
  Evaluation.sections ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (profiniteCoefficient Λ.X (affineComponentSpace W)) (componentAffineObject W U)

/-- Actual module evaluation on a pro-etale test, with its pulled-back condensed scalars.
Source: HRS (4.2) (blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
abbrev componentTargetSections (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (W : Scheme.{u}) (U : W.ProEt) :=
  Evaluation.sections (Scheme.ProEt.topology W) (condensedRingObj Λ.X W) U

private theorem component_split_covers (W : Scheme.{u}) [IsAffine W]
    (U : W.ProEt) [IsAffine U.left] [IsWContractibleRing Γ(U.left, ⊤)] :
    Scheme.ProEt.HasSplitFiniteQcqsCovers
      (⟨U, inferInstance, inferInstance⟩ : Scheme.ProEt.Qcqs W) := by
  classical
  intro n V a ha
  have hb : WeaklyEtale (Sigma.desc (fun i ↦ (V i).obj.hom)) :=
    IsZariskiLocalAtSource.sigmaDesc (fun i ↦ (V i).obj.prop)
  let B : W.ProEt := Scheme.ProEt.mk (Sigma.desc (fun i ↦ (V i).obj.hom))
  let j (i : Fin n) : (V i).obj ⟶ B :=
    MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (V i).obj.left) i) (by
      simp [B])
  let p : B ⟶ U := MorphismProperty.Over.homMk
    (Sigma.desc (fun i ↦ (a i).left)) (by
      apply Sigma.hom_ext
      intro i
      change Sigma.ι _ i ≫ Sigma.desc _ ≫ U.hom =
        Sigma.ι _ i ≫ Sigma.desc _
      simp only [Sigma.ι_desc_assoc, Sigma.ι_desc]
      exact (a i).w)
  have hj (i : Fin n) : j i ≫ p = a i := by
    apply MorphismProperty.Over.Hom.ext
    exact Sigma.ι_desc _ i
  let J := Scheme.ProEt.topology W
  let Y := J.uliftYoneda.{u + 1}
  have hp : Sieve.generate (Presieve.singleton p) ∈ J U := by
    apply J.superset_covering _ (Scheme.ProEt.mem_topology_iff.mpr
      ⟨_, ha, Sieve.le_generate _⟩)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro Z f ⟨i⟩
    rw [← hj i]
    exact (Sieve.generate (Presieve.singleton p)).downward_closed
      ((Sieve.le_generate (Presieve.singleton p) _) _ (Presieve.singleton_self p)) _
  have hsurj : Sheaf.IsLocallySurjective (Y.map p) := by
    constructor
    intro Z z
    apply J.superset_covering _ (J.pullback_stable z.down hp)
    intro T f hf
    obtain ⟨R, g, h, hh, heq⟩ := hf
    cases hh
    exact ⟨ULift.up g, by
      apply ULift.ext
      exact heq⟩
  have hU := Scheme.ProEt.isWeaklyContractible_of_iso
    (T := W) (W := U) U.left.isoSpec
  obtain ⟨σ, hσ⟩ := hU (Y.map p) hsurj (ULift.up (𝟙 U))
  refine ⟨σ.down.left, ?_⟩
  exact congrArg (fun f : U ⟶ U ↦ f.left) (congrArg ULift.down hσ)

private def componentLift (W : Scheme.{u}) [IsAffine W]
    (U : W.ProEt) [IsAffine U.left] :
    U ⟶ (componentTests W).obj (componentAffineObject W U) := by
  let hp := (component_relative_profinite_site W).choose_spec.2.1.choose_spec
  let g : C(U.left, (componentAffineObject W U).left) :=
    ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  exact MorphismProperty.Over.homMk
    (hp.2.2 ((Scheme.ProEt.forget W).obj U) _ g (fun _ ↦ rfl)).choose.left
    (hp.2.2 ((Scheme.ProEt.forget W).obj U) _ g (fun _ ↦ rfl)).choose.w

private theorem componentLift_projection (W : Scheme.{u}) [IsAffine W]
    (U : W.ProEt) [IsAffine U.left] (x : U.left) :
    componentTestProjection W (componentAffineObject W U) ((componentLift W U).left x) =
      ConnectedComponents.mk x := by
  exact ((component_relative_profinite_site W).choose_spec.2.1.choose_spec.2.2
    ((Scheme.ProEt.forget W).obj U) (componentAffineObject W U)
    ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
    (fun _ ↦ rfl)).choose_spec.1 x

private theorem componentLift_ext (W : Scheme.{u}) [IsAffine W]
    (U : W.ProEt) (E : Over (affineComponentSpace W))
    (a b : U ⟶ (componentTests W).obj E)
    (h : ∀ x : U.left, componentTestProjection W E (a.left x) =
      componentTestProjection W E (b.left x)) : a = b := by
  let hp := (component_relative_profinite_site W).choose_spec.2.1.choose_spec
  let g : C(U.left, E.left) := (componentTestProjection W E).comp
    ⟨b.left, b.left.continuous⟩
  have hg (x : U.left) : E.hom (g x) = ConnectedComponents.mk (U.hom x) :=
    (hp.1 E _).trans (congrArg ConnectedComponents.mk
      (congrArg (fun f ↦ f x) b.w))
  apply (Scheme.ProEt.forget W).map_injective
  exact (hp.2.2 ((Scheme.ProEt.forget W).obj U) E g hg).unique h (fun _ ↦ rfl)

private theorem componentLift_factor (W : Scheme.{u}) [IsAffine W]
    (U : W.ProEt) [IsAffine U.left] (E : Over (affineComponentSpace W))
    (b : U ⟶ (componentTests W).obj E) (c : componentAffineObject W U ⟶ E)
    (h : ∀ x : U.left, componentTestProjection W E (b.left x) =
      c.left (ConnectedComponents.mk x)) :
    componentLift W U ≫ (componentTests W).map c = b := by
  apply componentLift_ext
  intro x
  change componentTestProjection W E
    (((componentTests W).map c).left ((componentLift W U).left x)) = _
  exact ((component_relative_profinite_site W).choose_spec.2.1.choose_spec.2.1
    (componentAffineObject W U) E c ((componentLift W U).left x)).trans
      ((congrArg c.left (componentLift_projection W U x)).trans (h x).symm)

private theorem componentLift_naturality (W : Scheme.{u}) [IsAffine W]
    {U V : W.ProEt} [IsAffine U.left] [IsAffine V.left] (f : U ⟶ V) :
    componentLift W U ≫ (componentTests W).map (componentAffineObjectMap f) =
      f ≫ componentLift W V := by
  apply componentLift_factor
  intro x
  change componentTestProjection W (componentAffineObject W V)
    ((componentLift W V).left (f.left x)) =
      (componentAffineObjectMap f).left (ConnectedComponents.mk x)
  rw [componentLift_projection]
  rfl

private instance component_evaluationMonoidal {C A : Type*} [Category C] [Category A]
    [MonoidalCategory A] (U : C) : ((evaluation C A).obj U).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

private instance component_evaluationBraided {C A : Type*} [Category C] [Category A]
    [MonoidalCategory A] [BraidedCategory A] (U : C) :
    ((evaluation C A).obj U).Braided where
  braided X Y := by
    change (𝟙 _ ≫ _) = (_ ≫ 𝟙 _)
    simp only [Category.id_comp, Category.comp_id]
    rfl

private abbrev componentSections {C : Type*} [Category C] (J : GrothendieckTopology C)
    (U : C) := sheafToPresheaf J Ab.{u + 1} ⋙ (evaluation Cᵒᵖ Ab.{u + 1}).obj (op U)

section AbelianEvaluation
variable (W : Scheme.{u}) [IsAffine W]
  [(componentTests W).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)]

private instance componentTests_limits : PreservesFiniteLimits (componentTests W) :=
  (component_relative_profinite_site W).choose_spec.2.2.2.2.2.1

private instance componentTests_flat : RepresentablyFlat (componentTests W) :=
  flat_of_preservesFiniteLimits _

@[instance_reducible] private def componentCanonicalBraided : (componentInverse W).Braided := by
  let : (componentInverse W).Monoidal := by dsimp only [componentInverse]; infer_instance
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentTests W)
    Ab.{u + 1} ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)
  exact { braided := fun X Y ↦ adj.μ_comp_map_braiding X Y }

private def componentPushforwardSections (E : Over (affineComponentSpace W)) :
    (componentTests W).sheafPushforwardContinuous Ab.{u + 1}
        ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
        (Scheme.ProEt.topology W) ⋙
      componentSections ((coherentTopology Profinite.{u}).over (affineComponentSpace W)) E ≅
        componentSections (Scheme.ProEt.topology W) ((componentTests W).obj E) :=
  Functor.isoWhiskerRight
    (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      (componentTests W) Ab.{u + 1}
      ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
      (Scheme.ProEt.topology W)).symm ((evaluation _ Ab.{u + 1}).obj (op E))

private instance componentPushforwardSections_monoidal (E : Over (affineComponentSpace W)) :
    NatTrans.IsMonoidal (componentPushforwardSections W E).hom := by
  dsimp only [componentPushforwardSections, Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

private def componentSectionMap (U : W.ProEt) [IsAffine U.left] :
    componentSections ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
        (componentAffineObject W U) ⟶
      componentInverse W ⋙ componentSections (Scheme.ProEt.topology W) U :=
  Functor.whiskerRight
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentTests W)
      Ab.{u + 1} ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
      (Scheme.ProEt.topology W)).unit
    (componentSections ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
      (componentAffineObject W U)) ≫
    Functor.whiskerLeft (componentInverse W)
      ((componentPushforwardSections W (componentAffineObject W U)).hom ≫
        (sheafSections (Scheme.ProEt.topology W) Ab.{u + 1}).map (componentLift W U).op)

private theorem componentSectionMap_formula (U : W.ProEt) [IsAffine U.left]
    (M : Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace W)) Ab.{u + 1}) :
    (componentSectionMap W U).app M =
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentTests W)
        Ab.{u + 1} ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
        (Scheme.ProEt.topology W)).unit.app M).hom.app (op (componentAffineObject W U)) ≫
          ((componentInverse W).obj M).obj.map (componentLift W U).op := by
  simp only [componentSectionMap, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  have h := (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    (componentTests W) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)).hom_inv_id_app ((componentInverse W).obj M)
  rw [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
    Category.id_comp] at h
  dsimp only [componentPushforwardSections, Functor.isoWhiskerRight_hom, Iso.symm_hom]
  dsimp only [Functor.whiskerRight_app]
  change _ ≫ ((evaluation _ Ab.{u + 1}).obj _).map
    ((Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      (componentTests W) Ab.{u + 1}
      ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
      (Scheme.ProEt.topology W)).inv.app ((componentInverse W).obj M)) ≫ _ = _
  rw [h]
  rfl

private instance componentSheafSectionsMonoidal {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] (U : C) :
    ((sheafSections J Ab.{u + 1}).obj (op U)).LaxMonoidal :=
  inferInstanceAs (componentSections J U).LaxMonoidal

private theorem componentSectionsMap_monoidal {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] {T U : C} (f : T ⟶ U) :
    NatTrans.IsMonoidal ((sheafSections J Ab.{u + 1}).map f.op) := by
  constructor
  · with_unfolding_all change (𝟙 _ ≫ _) ≫ _ = 𝟙 _ ≫ _
    simpa using ((Functor.LaxMonoidal.ε
      (sheafToPresheaf J Ab.{u + 1})).naturality f.op).symm
  · intro P Q
    with_unfolding_all change (𝟙 _ ≫ _) ≫ _ = _ ≫ (𝟙 _ ≫ _)
    simpa using ((Functor.LaxMonoidal.μ
      (sheafToPresheaf J Ab.{u + 1}) P Q).naturality f.op).symm

private theorem componentSectionMap_monoidal (U : W.ProEt) [IsAffine U.left] :
    let := componentCanonicalBraided W
    NatTrans.IsMonoidal (componentSectionMap W U) := by
  let := componentCanonicalBraided W
  let := componentSectionsMap_monoidal (Scheme.ProEt.topology W) (componentLift W U)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (componentTests W) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)
  have : NatTrans.IsMonoidal adj.unit := by
    dsimp only [adj]
    infer_instance
  dsimp only [componentSectionMap]
  infer_instance

private theorem componentSectionMap_normalization (U : W.ProEt) [IsAffine U.left]
    (M : Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace W)) Ab.{u + 1})
    (E : Over (affineComponentSpace W)) (b : U ⟶ (componentTests W).obj E)
    (c : componentAffineObject W U ⟶ E)
    (h : ∀ x : U.left, componentTestProjection W E (b.left x) =
      c.left (ConnectedComponents.mk x)) :
    M.obj.map c.op ≫ (componentSectionMap W U).app M =
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentTests W)
        Ab.{u + 1} ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
        (Scheme.ProEt.topology W)).unit.app M).hom.app (op E) ≫
          ((componentInverse W).obj M).obj.map b.op := by
  rw [componentSectionMap_formula, ← Category.assoc]
  have hn := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentTests W)
    Ab.{u + 1} ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)).unit.app M).hom.naturality c.op
  dsimp only [Functor.id_obj] at hn
  rw [hn]
  change _ ≫ ((componentInverse W).obj M).obj.map
    ((componentTests W).map c).op ≫ _ = _
  rw [← CategoryTheory.Functor.map_comp, ← op_comp,
    componentLift_factor W U E b c h]

private theorem componentSectionMap_naturality (U V : W.ProEt)
    [IsAffine U.left] [IsAffine V.left] (f : U ⟶ V)
    (M : Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace W)) Ab.{u + 1}) :
    M.obj.map (componentAffineObjectMap f).op ≫ (componentSectionMap W U).app M =
      (componentSectionMap W V).app M ≫ ((componentInverse W).obj M).obj.map f.op := by
  have h := componentSectionMap_normalization W U M (componentAffineObject W V)
    (f ≫ componentLift W V) (componentAffineObjectMap f) (by
      intro x
      change componentTestProjection W (componentAffineObject W V)
        ((componentLift W V).left (f.left x)) = _
      rw [componentLift_projection]
      rfl)
  simpa only [componentSectionMap_formula, op_comp, Functor.map_comp, Category.assoc] using h

private theorem componentSectionMap_isIso (U : W.ProEt) [IsAffine U.left]
    [IsWContractibleRing Γ(U.left, ⊤)]
    (M : Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace W)) Ab.{u + 1}) :
    IsIso ((componentSectionMap W U).app M) := by
  classical
  let A := (Scheme.ProEt.affine_component_site_projection W).choose
  let r := (Scheme.ProEt.affine_component_site_projection W).choose_spec.choose
  have hA := (Scheme.ProEt.affine_component_site_projection W).choose_spec.choose_spec
  obtain ⟨hcont, _, hAb, _⟩ := hA.2.2.2.2
  let : A.IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
      (Scheme.ProEt.topology W) := hcont
  obtain ⟨g, d, b, hb, e, he, _⟩ := hAb
  obtain ⟨θ, hθ, _⟩ := relative_component_lift_pullback_space W
  let t : componentTests W ≅ A :=
    Functor.fullyFaithfulCancelRight (Scheme.ProEt.forget W) θ
  let q := d ≪≫ Functor.sheafPushforwardContinuousIso t.symm Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (componentTests W) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)
  let k : componentInverse W ≅ g.inverse := adj.leftAdjointUniq (g.adj.ofNatIsoRight q)
  let Uq : Scheme.ProEt.Qcqs W := ⟨U, inferInstance, inferInstance⟩
  let a : U ⟶ A.obj (componentAffineObject W U) :=
    componentLift W U ≫ t.hom.app (componentAffineObject W U)
  have hcoord (x : U.left) : r _ (a.left x) = ConnectedComponents.mk x := by
    have ht : (Scheme.ProEt.forget W).map (t.hom.app (componentAffineObject W U)) =
        θ.hom.app (componentAffineObject W U) := by
      dsimp only [t]
      simp only [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
    change r _ ((t.hom.app _).left ((componentLift W U).left x)) = _
    rw [show (t.hom.app (componentAffineObject W U)).left =
      (θ.hom.app (componentAffineObject W U)).left from congrArg Over.Hom.left ht]
    exact (hθ _ _).trans (componentLift_projection W U x)
  have hba : b Uq _ a = 𝟙 (componentAffineObject W U) := by
    apply Over.OverMorphism.ext
    apply ConcreteCategory.hom_ext
    intro z
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
    exact (hb Uq _ a x).trans (hcoord x)
  let v := ((sheafToPresheaf (Scheme.ProEt.topology W) Ab.{u + 1} ⋙
    (evaluation _ Ab.{u + 1}).obj (op U)).mapIso (k.app M)) ≪≫
      e M Uq (component_split_covers W U)
  have hv : (componentSectionMap W U).app M ≫ v.hom = 𝟙 _ := by
    rw [componentSectionMap_formula]
    have hunit := adj.unit_leftAdjointUniq_hom_app (g.adj.ofNatIsoRight q) M
    have hunit' := congrArg (fun f : M ⟶
        ((componentTests W).sheafPushforwardContinuous Ab.{u + 1}
          ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
          (Scheme.ProEt.topology W)).obj (g.inverse.obj M) ↦
        f.hom.app (op (componentAffineObject W U))) hunit
    change (adj.unit.app M).hom.app (op (componentAffineObject W U)) ≫
      (k.hom.app M).hom.app (op ((componentTests W).obj (componentAffineObject W U))) =
        ((g.adj.unit.app M ≫ d.hom.app (g.inverse.obj M)).hom.app
          (op (componentAffineObject W U))) ≫
            (g.inverse.obj M).obj.map (t.hom.app (componentAffineObject W U)).op at hunit'
    have hnat := (k.hom.app M).hom.naturality (componentLift W U).op
    change (_ ≫ _) ≫ ((k.hom.app M).hom.app (op U) ≫ _) = _
    rw [Category.assoc, ← Category.assoc _ ((k.hom.app M).hom.app (op U)), hnat,
      Category.assoc, ← Category.assoc, hunit']
    have hh := he M Uq (component_split_covers W U) (componentAffineObject W U) a
    rw [hba] at hh
    have hi : M.obj.map (𝟙 (componentAffineObject W U)).op = 𝟙 _ :=
      M.obj.map_id _
    apply Eq.trans _ hi
    simpa only [a, op_comp, CategoryTheory.Functor.map_comp, Category.assoc] using hh
  have : IsIso ((componentSectionMap W U).app M ≫ v.hom) := by
    rw [hv]
    infer_instance
  exact IsIso.of_isIso_comp_right _ v.hom

end AbelianEvaluation

section Comparison

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (W : Scheme.{u}) [IsAffine W]
  [(componentTests W).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)]
  [(componentInverse W).Braided]
  [PreservesFiniteLimits (componentInverse W)]
  [PreservesFiniteColimits (componentInverse W)]
  (α : (componentInverse W).mapMon.obj
    (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace W))) ≅
      Mon.mk (condensedRingObj Λ.X W))

/-- A coefficient comparison at a test is an isomorphism of the actual section rings.
Source: HRS (4.2) (blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
abbrev ComponentEvaluationRingIso (U : W.ProEt) [IsAffine U.left] :=
  Evaluation.A ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
      (profiniteCoefficient Λ.X (affineComponentSpace W)) (componentAffineObject W U) ≅
    Evaluation.A (Scheme.ProEt.topology W) (condensedRingObj Λ.X W) U

/-- Pullback followed by evaluation, viewed over the source section ring by scalar transport.
Source: HRS (4.2) (blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
abbrev componentEvaluationTarget (U : W.ProEt) [IsAffine U.left]
    (a : ComponentEvaluationRingIso Λ W U) :=
  componentModules Λ.X W α ⋙ componentTargetSections Λ W U ⋙
    ModuleCat.restrictScalars.{u + 1} a.hom.hom

/-- Right derived evaluation with its section-module universe fixed explicitly.
Source: HRS Section 3 (blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
abbrev componentSourceDerivedSections (U : W.ProEt) [IsAffine U.left] :
    Evaluation.D ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
        (profiniteCoefficient Λ.X (affineComponentSpace W)) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        (Evaluation.A ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
          (profiniteCoefficient Λ.X (affineComponentSpace W)) (componentAffineObject W U))) :=
  (componentSourceSections Λ W U).rightDerivedFunctor

/-- Right derived evaluation over the actual coefficient ring on the scheme test.
Source: HRS Section 3 (blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
abbrev componentTargetDerivedSections (U : W.ProEt) :
    Evaluation.D (Scheme.ProEt.topology W) (condensedRingObj Λ.X W) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        (Evaluation.A (Scheme.ProEt.topology W) (condensedRingObj Λ.X W) U)) :=
  (componentTargetSections Λ W U).rightDerivedFunctor

/-- The derived comparison constructed from the displayed module comparison. Every functor
is the ordinary unbounded one. The formula uses exact-functor localization and the canonical
comparison of right derivation with termwise evaluation, so fixes every representative.
Source: HRS (4.2), Section 3
(blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
def componentEvaluationDerivedIso (U : W.ProEt) [IsAffine U.left]
    (a : ComponentEvaluationRingIso Λ W U)
    [PreservesFiniteLimits (componentSourceSections Λ W U)]
    [PreservesFiniteColimits (componentSourceSections Λ W U)]
    [PreservesFiniteLimits (componentTargetSections Λ W U)]
    [PreservesFiniteColimits (componentTargetSections Λ W U)]
    (e : componentSourceSections Λ W U ≅ componentEvaluationTarget Λ W α U a) :
    componentSourceDerivedSections Λ W U ≅
      componentDerived Λ.X W α ⋙ componentTargetDerivedSections Λ W U ⋙
        (ModuleCat.restrictScalars.{u + 1} a.hom.hom).mapDerivedCategory.{u + 1, u + 1} :=
  (componentSourceSections Λ W U).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryCompIso (componentModules Λ.X W α)
      (componentTargetSections Λ W U ⋙ ModuleCat.restrictScalars.{u + 1} a.hom.hom) ≪≫
    Functor.isoWhiskerLeft (componentDerived Λ.X W α)
      (Functor.mapDerivedCategoryCompIso (componentTargetSections Λ W U)
        (ModuleCat.restrictScalars.{u + 1} a.hom.hom) ≪≫
        Functor.isoWhiskerRight
          (componentTargetSections Λ W U).rightDerivedFunctorIsoMapDerivedCategory.symm
          (ModuleCat.restrictScalars.{u + 1} a.hom.hom).mapDerivedCategory.{u + 1, u + 1})

/-- The abelian pullback adjunction used to normalize all section comparisons.
Source: HRS (4.1)--(4.2), Stacks Tags 00VE and 00WX
(blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
abbrev componentAbelianAdjunction :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentTests W) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)

/-- The evaluation assertion includes both naturality variables and normalization on every
Kan coprojection. Exact evaluations compute right derived sections termwise on arbitrary
unbounded complexes. The derived isomorphism below is a defined entire-object comparison,
not a family of cohomology isomorphisms.
Source: HRS Section 3, Proposition 4.3(1), (4.2)
(blueprint: lem-sfb-component-pullback-unbounded-evaluation). -/
def ComponentPullbackUnboundedEvaluation : Prop :=
  ∃ a : ∀ (U : W.ProEt) [IsAffine U.left] [IsWContractibleRing Γ(U.left, ⊤)],
      ComponentEvaluationRingIso Λ W U,
    ∃ e : ∀ (U : W.ProEt) [IsAffine U.left] [IsWContractibleRing Γ(U.left, ⊤)],
        componentSourceSections Λ W U ≅ componentEvaluationTarget Λ W α U (a U),
      (∀ (U V : W.ProEt) [IsAffine U.left] [IsAffine V.left]
        [IsWContractibleRing Γ(U.left, ⊤)] [IsWContractibleRing Γ(V.left, ⊤)]
        (f : U ⟶ V)
        (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
          Ab.{u + 1}) (profiniteCoefficient Λ.X (affineComponentSpace W)))
        (x : M.X.obj.obj (op (componentAffineObject W V))),
        (e U).hom.app M (M.X.obj.map (componentAffineObjectMap f).op x) =
          ((componentModules Λ.X W α).obj M).X.obj.map f.op ((e V).hom.app M x)) ∧
      (∀ (U : W.ProEt) [IsAffine U.left] [IsWContractibleRing Γ(U.left, ⊤)]
        (E : Over (affineComponentSpace W)) (b : U ⟶ (componentTests W).obj E)
        (c : componentAffineObject W U ⟶ E),
        (∀ x : U.left,
          componentTestProjection W E (b.left x) = c.left (ConnectedComponents.mk x)) →
        (∀ x : (profiniteCoefficient Λ.X (affineComponentSpace W)).obj.obj (op E),
          (a U).hom ((profiniteCoefficient Λ.X (affineComponentSpace W)).obj.map c.op x) =
            α.hom.hom.hom.app (op U)
              (((componentInverse W).obj
                (profiniteCoefficient Λ.X (affineComponentSpace W))).obj.map b.op
                (((componentAbelianAdjunction W).unit.app
                  (profiniteCoefficient Λ.X (affineComponentSpace W))).hom.app (op E) x))) ∧
        ∀ (M : Mod
          (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace W)) Ab.{u + 1})
          (profiniteCoefficient Λ.X (affineComponentSpace W)))
          (x : M.X.obj.obj (op E)),
          (e U).hom.app M (M.X.obj.map c.op x) =
            ((componentInverse W).obj M.X).obj.map b.op
              (((componentAbelianAdjunction W).unit.app M.X).hom.app (op E) x)) ∧
      ∀ (U : W.ProEt) [IsAffine U.left] [IsWContractibleRing Γ(U.left, ⊤)],
        ∃ (_ : PreservesFiniteLimits (componentSourceSections Λ W U))
          (_ : PreservesFiniteColimits (componentSourceSections Λ W U))
          (_ : PreservesFiniteLimits (componentTargetSections Λ W U))
          (_ : PreservesFiniteColimits (componentTargetSections Λ W U)),
          IsIso (componentSourceSections Λ W U).rightDerivedFunctorUnit ∧
          IsIso (componentTargetSections Λ W U).rightDerivedFunctorUnit ∧
          ∃ δ : componentSourceDerivedSections Λ W U ≅
            componentDerived Λ.X W α ⋙ componentTargetDerivedSections Λ W U ⋙
              (ModuleCat.restrictScalars.{u + 1} (a U).hom.hom).mapDerivedCategory.{u + 1, u + 1},
            δ = componentEvaluationDerivedIso Λ W α U (a U) (e U)

end Comparison
set_option backward.isDefEq.respectTransparency true

private theorem componentSections_smul
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (M : Mod (Sheaf J Ab.{u + 1}) O)
    (r : Evaluation.A J O U) (x : (Evaluation.sections J O U).obj M) :
    r • x = (Functor.LaxMonoidal.μ (componentSections J U) O M.X ≫
      (componentSections J U).map (Mod.act M.X)).hom (r ⊗ₜ[ℤ] x) := by
  rfl

private theorem componentSections_comap_smul
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (A B : Sheaf J Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    [MonObj B] [IsCommMonObj B] (f : A ⟶ B) [IsMonHom f]
    (U : C) (M : Mod (Sheaf J Ab.{u + 1}) B)
    (r : Evaluation.A J A U) (x : (Evaluation.sections J A U).obj ((Mod.comap f).obj M)) :
    r • x = (f.hom.app (op U) r) •
      (show (Evaluation.sections J B U).obj M from x) := by
  rw [componentSections_smul]
  change _ = (Functor.LaxMonoidal.μ (componentSections J U) B M.X ≫
    (componentSections J U).map (Mod.act M.X)).hom
      (f.hom.app (op U) r ⊗ₜ[ℤ] x)
  have h := Functor.LaxMonoidal.μ_natural_left_assoc
    (componentSections J U) f M.X (componentSections J U |>.map (Mod.act M.X))
  change (Functor.LaxMonoidal.μ (componentSections J U) A M.X ≫
    (componentSections J U).map (f ▷ M.X ≫ Mod.act M.X)).hom (r ⊗ₜ[ℤ] x) = _
  rw [Functor.map_comp, ← h]
  rfl

private theorem componentSections_mapMod_smul
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [(J.W (A := Ab.{u + 1})).IsMonoidal] [(K.W (A := Ab.{u + 1})).IsMonoidal]
    (F : Sheaf J Ab.{u + 1} ⥤ Sheaf K Ab.{u + 1}) [F.Braided]
    (A : Sheaf J Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (V : D) (M : Mod (Sheaf J Ab.{u + 1}) A)
    (r : Evaluation.A K (F.obj A) V)
    (x : (Evaluation.sections K (F.obj A) V).obj ((F.mapMod A).obj M)) :
    r • x = (Functor.LaxMonoidal.μ (F ⋙ componentSections K V) A M.X ≫
      (F ⋙ componentSections K V).map (Mod.act M.X)).hom (r ⊗ₜ[ℤ] x) := by
  rw [componentSections_smul, Functor.act_mapMod_obj]
  change (Functor.LaxMonoidal.μ (componentSections K V) (F.obj A) (F.obj M.X) ≫
    (componentSections K V).map
      (Functor.LaxMonoidal.μ F A M.X ≫ F.map (Mod.act M.X))).hom (r ⊗ₜ[ℤ] x) = _
  rw [Functor.map_comp]
  rfl

private def componentGenericRingIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [(J.W (A := Ab.{u + 1})).IsMonoidal] [(K.W (A := Ab.{u + 1})).IsMonoidal]
    (F : Sheaf J Ab.{u + 1} ⥤ Sheaf K Ab.{u + 1}) [F.Braided]
    (A : Sheaf J Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (B : Sheaf K Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
    (α : F.mapMon.obj (Mon.mk A) ≅ Mon.mk B) (U : C) (V : D)
    (e : componentSections J U ≅ F ⋙ componentSections K V)
    [NatTrans.IsMonoidal e.hom] : Evaluation.A J A U ≅ Evaluation.A K B V := by
  let E := componentSections J U
  let G := componentSections K V
  let m : E.mapMon.obj (Mon.mk A) ≅ G.mapMon.obj (Mon.mk B) :=
    (Functor.mapMonNatIso e).app (Mon.mk A) ≪≫
      (Functor.mapMonCompIso (F := F) (G := G)).app (Mon.mk A) ≪≫ G.mapMon.mapIso α
  let c : E.mapCommMon.obj (CommMon.mk A) ≅ G.mapCommMon.obj (CommMon.mk B) :=
    (CommMon.fullyFaithfulForget₂Mon Ab.{u + 1}).preimageIso m
  exact InternalAbelianSheafModule.commMonToRing.mapIso c

section GenericModuleComparison
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := Ab.{u + 1})).IsMonoidal] [(K.W (A := Ab.{u + 1})).IsMonoidal]
  (F : Sheaf J Ab.{u + 1} ⥤ Sheaf K Ab.{u + 1}) [F.Braided]
  (A : Sheaf J Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
  (B : Sheaf K Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
  (α : F.mapMon.obj (Mon.mk A) ≅ Mon.mk B) (U : C) (V : D)

private theorem componentGenericRingIso_apply
    (e : componentSections J U ≅ F ⋙ componentSections K V)
    [NatTrans.IsMonoidal e.hom] (r : Evaluation.A J A U) :
    (componentGenericRingIso J K F A B α U V e).hom r =
      α.hom.hom.hom.app (op V) (e.hom.app A r) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem componentGenericModule_smul
    (e : componentSections J U ≅ F ⋙ componentSections K V)
    [NatTrans.IsMonoidal e.hom] (M : Mod (Sheaf J Ab.{u + 1}) A)
    (r : Evaluation.A J A U) (x : (Evaluation.sections J A U).obj M) :
    e.hom.app M.X (r • x) =
      (componentGenericRingIso J K F A B α U V e).hom r •
        (show (Evaluation.sections K B V).obj
          ((Mod.comap α.inv.hom).obj ((F.mapMod A).obj M)) from e.hom.app M.X x) := by
  have h := ConcreteCategory.congr_hom
    (Mod.act_hom ((Functor.mapModNatTrans e.hom A).app M)) (r ⊗ₜ[ℤ] x)
  change e.hom.app M.X
    ((Functor.LaxMonoidal.μ (componentSections J U) A M.X ≫
      (componentSections J U).map (Mod.act M.X)).hom (r ⊗ₜ[ℤ] x)) =
    (Functor.LaxMonoidal.μ (F ⋙ componentSections K V) A M.X ≫
      (F ⋙ componentSections K V).map (Mod.act M.X)).hom
        (e.hom.app A r ⊗ₜ[ℤ] e.hom.app M.X x) at h
  have hs := componentSections_smul J A U M r x
  have ht := componentSections_mapMod_smul J K F A V M
    (e.hom.app A r) (e.hom.app M.X x)
  have ha : α.hom.hom.hom.app (op V) ≫ α.inv.hom.hom.app (op V) = 𝟙 _ :=
    congrArg (fun f ↦ f.hom.hom.app (op V)) α.hom_inv_id
  have hc := ConcreteCategory.congr_hom ha (e.hom.app A r)
  change α.inv.hom.hom.app (op V)
    (α.hom.hom.hom.app (op V) (e.hom.app A r)) = e.hom.app A r at hc
  have hr := componentSections_comap_smul K B (F.obj A) α.inv.hom V
    ((F.mapMod A).obj M) ((componentGenericRingIso J K F A B α U V e).hom r)
    (e.hom.app M.X x)
  have hr' :
      (componentGenericRingIso J K F A B α U V e).hom r •
        (show (Evaluation.sections K B V).obj
          ((Mod.comap α.inv.hom).obj ((F.mapMod A).obj M)) from e.hom.app M.X x) =
      (e.hom.app A r) •
        (show (Evaluation.sections K (F.obj A) V).obj ((F.mapMod A).obj M)
          from e.hom.app M.X x) := by
    refine hr.trans ?_
    exact congrArg (fun z : Evaluation.A K (F.obj A) V ↦
      z • (show (Evaluation.sections K (F.obj A) V).obj ((F.mapMod A).obj M)
        from e.hom.app M.X x))
      ((congrArg (fun z ↦ α.inv.hom.hom.app (op V) z)
        (componentGenericRingIso_apply J K F A B α U V e r)).trans hc)
  exact (congrArg (fun y ↦ e.hom.app M.X y) hs).trans (h.trans (ht.symm.trans hr'.symm))

set_option backward.isDefEq.respectTransparency false in
private def componentGenericModuleComparison
    (e : componentSections J U ≅ F ⋙ componentSections K V)
    [NatTrans.IsMonoidal e.hom] :
    Evaluation.sections J A U ⟶
      (F.mapMod A ⋙ Mod.comap α.inv.hom) ⋙ Evaluation.sections K B V ⋙
        ModuleCat.restrictScalars (componentGenericRingIso J K F A B α U V e).hom.hom where
  app M := by
    let S := (Evaluation.sections J A U).obj M
    let T : ModuleCat.{u + 1} (Evaluation.A J A U) :=
      (ModuleCat.restrictScalars (componentGenericRingIso J K F A B α U V e).hom.hom).obj
        ((Evaluation.sections K B V).obj ((Mod.comap α.inv.hom).obj ((F.mapMod A).obj M)))
    refine ModuleCat.ofHom (X := S) (Y := T) (show S →ₗ[Evaluation.A J A U] T from ?_)
    exact
    { toFun := fun x ↦ e.hom.app M.X x
      map_add' := fun x y ↦ map_add _ x y
      map_smul' := by
        intro r x
        exact componentGenericModule_smul J K F A B α U V e M r x }
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (e.hom.naturality f.hom) x

end GenericModuleComparison

section CanonicalComparison
variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (W : Scheme.{u}) [IsAffine W]
  [(componentTests W).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)]

variable [(componentInverse W).Braided]

variable (α : (componentInverse W).mapMon.obj
    (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace W))) ≅
      Mon.mk (condensedRingObj Λ.X W))

private def componentRingComparison
    (hmono : ∀ (U : W.ProEt) [IsAffine U.left],
      NatTrans.IsMonoidal (componentSectionMap W U))
    (α : (componentInverse W).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace W))) ≅
        Mon.mk (condensedRingObj Λ.X W)) (U : W.ProEt) [IsAffine U.left]
    [IsWContractibleRing Γ(U.left, ⊤)] : ComponentEvaluationRingIso Λ W U := by
  letI : NatTrans.IsMonoidal (componentSectionMap W U) := hmono U
  letI : ∀ M, IsIso ((componentSectionMap W U).app M) := componentSectionMap_isIso W U
  letI : IsIso (componentSectionMap W U) := NatIso.isIso_of_isIso_app _
  letI : NatTrans.IsMonoidal (asIso (componentSectionMap W U)).hom := hmono U
  exact componentGenericRingIso
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W) (componentInverse W)
    (profiniteCoefficient Λ.X (affineComponentSpace W)) (condensedRingObj Λ.X W)
    α (componentAffineObject W U) U (asIso (componentSectionMap W U))

private def componentModuleComparison
    (hmono : ∀ (U : W.ProEt) [IsAffine U.left],
      NatTrans.IsMonoidal (componentSectionMap W U)) (U : W.ProEt) [IsAffine U.left]
    [IsWContractibleRing Γ(U.left, ⊤)] :
    componentSourceSections Λ W U ⟶
      componentEvaluationTarget Λ W α U (componentRingComparison Λ W hmono α U) := by
  letI : NatTrans.IsMonoidal (componentSectionMap W U) := hmono U
  letI : ∀ M, IsIso ((componentSectionMap W U).app M) := componentSectionMap_isIso W U
  letI : IsIso (componentSectionMap W U) := NatIso.isIso_of_isIso_app _
  letI : NatTrans.IsMonoidal (asIso (componentSectionMap W U)).hom := hmono U
  exact componentGenericModuleComparison
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W) (componentInverse W)
    (profiniteCoefficient Λ.X (affineComponentSpace W)) (condensedRingObj Λ.X W)
    α (componentAffineObject W U) U (asIso (componentSectionMap W U))

private theorem componentModuleComparison_underlying
    (hmono : ∀ (U : W.ProEt) [IsAffine U.left],
      NatTrans.IsMonoidal (componentSectionMap W U)) (U : W.ProEt) [IsAffine U.left]
    [IsWContractibleRing Γ(U.left, ⊤)]
    (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
      Ab.{u + 1}) (profiniteCoefficient Λ.X (affineComponentSpace W))) :
    (CategoryTheory.forget₂
      (ModuleCat.{u + 1} (Evaluation.A
        ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
        (profiniteCoefficient Λ.X (affineComponentSpace W)) (componentAffineObject W U)))
      Ab.{u + 1}).map ((componentModuleComparison Λ W α hmono U).app M) =
        (componentSectionMap W U).app M.X := by
  rfl

include α in
private def componentModuleIso
    (hmono : ∀ (U : W.ProEt) [IsAffine U.left],
      NatTrans.IsMonoidal (componentSectionMap W U)) (U : W.ProEt) [IsAffine U.left]
    [IsWContractibleRing Γ(U.left, ⊤)] :
    componentSourceSections Λ W U ≅
      componentEvaluationTarget Λ W α U (componentRingComparison Λ W hmono α U) := by
  have : ∀ M : Mod (Sheaf
      ((coherentTopology Profinite.{u}).over (affineComponentSpace W)) Ab.{u + 1})
      (profiniteCoefficient Λ.X (affineComponentSpace W)),
      IsIso ((componentModuleComparison Λ W α hmono U).app M) := by
    intro M
    let F := CategoryTheory.forget₂
      (ModuleCat.{u + 1} (Evaluation.A
        ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
        (profiniteCoefficient Λ.X (affineComponentSpace W)) (componentAffineObject W U)))
      Ab.{u + 1}
    have : IsIso (F.map ((componentModuleComparison Λ W α hmono U).app M)) := by
      change IsIso ((CategoryTheory.forget₂ _ Ab.{u + 1}).map
        ((componentModuleComparison Λ W α hmono U).app M))
      rw [componentModuleComparison_underlying]
      exact componentSectionMap_isIso W U M.X
    exact isIso_of_reflects_iso _ F
  letI : IsIso (componentModuleComparison Λ W α hmono U) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (componentModuleComparison Λ W α hmono U)

omit [IsAffine W]
  [(componentTests W).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)] [(componentInverse W).Braided] in
private theorem componentTarget_exact (U : W.ProEt) [IsAffine U.left]
    [IsWContractibleRing Γ(U.left, ⊤)] :
    PreservesFiniteLimits (componentTargetSections Λ W U) ∧
      PreservesFiniteColimits (componentTargetSections Λ W U) := by
  let ev : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1} ⥤ Ab.{u + 1} :=
    componentSections (Scheme.ProEt.topology W) U
  have : ev.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits ev := by dsimp only [ev, componentSections]; infer_instance
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    have : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' Ab.{u + 1} f).mpr hf
    let f' := (sheafCompose (Scheme.ProEt.topology W) (CategoryTheory.forget Ab.{u + 1})).map f
    exact (AddCommGrpCat.epi_iff_surjective (ev.map f)).mpr
      (Scheme.ProEt.isWeaklyContractible_of_iso
        (T := W) (W := U) U.left.isoSpec f' inferInstance)
  have : ev.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels ev
  have : PreservesFiniteColimits ev :=
    Functor.preservesFiniteColimits_of_preservesHomology ev
  let R := Evaluation.A (Scheme.ProEt.topology W) (condensedRingObj Λ.X W) U
  let F : ModuleCat.{u + 1} R ⥤ Ab.{u + 1} :=
    CategoryTheory.forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}
  have : ReflectsFiniteColimits F :=
    { reflects := fun _ _ _ ↦ inferInstance }
  have : PreservesFiniteLimits (componentTargetSections Λ W U ⋙ F) :=
    inferInstanceAs (PreservesFiniteLimits (Mod.forget (condensedRingObj Λ.X W) ⋙ ev))
  have : PreservesFiniteColimits (componentTargetSections Λ W U ⋙ F) :=
    inferInstanceAs (PreservesFiniteColimits (Mod.forget (condensedRingObj Λ.X W) ⋙ ev))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ F,
    preservesFiniteColimits_of_reflects_of_preserves _ F⟩

include α in
set_option backward.isDefEq.respectTransparency false in
private theorem componentCanonical_evaluation
    (hmono : ∀ (U : W.ProEt) [IsAffine U.left],
      NatTrans.IsMonoidal (componentSectionMap W U))
    [PreservesFiniteLimits (componentInverse W)]
    [PreservesFiniteColimits (componentInverse W)] :
    ComponentPullbackUnboundedEvaluation Λ W α := by
  let a := componentRingComparison Λ W hmono α
  let e := componentModuleIso Λ W α hmono
  refine Exists.intro a ?_
  refine Exists.intro e ?_
  refine ⟨?_, ?_, ?_⟩
  · intro U V _ _ _ _ f M x
    change ((componentSectionMap W U).app M.X)
      (M.X.obj.map (componentAffineObjectMap f).op x) =
        ((componentInverse W).obj M.X).obj.map f.op ((componentSectionMap W V).app M.X x)
    exact ConcreteCategory.congr_hom (componentSectionMap_naturality W U V f M.X) x
  · intro U _ _ E b c h
    constructor
    · intro x
      change α.hom.hom.hom.app (op U)
        (((componentSectionMap W U).app (profiniteCoefficient Λ.X (affineComponentSpace W)))
          ((profiniteCoefficient Λ.X (affineComponentSpace W)).obj.map c.op x)) = _
      exact congrArg (α.hom.hom.hom.app (op U))
        (ConcreteCategory.congr_hom (componentSectionMap_normalization W U
          (profiniteCoefficient Λ.X (affineComponentSpace W)) E b c h) x)
    · intro M x
      change ((componentSectionMap W U).app M.X) (M.X.obj.map c.op x) = _
      exact ConcreteCategory.congr_hom
        (componentSectionMap_normalization W U M.X E b c h) x
  · intro U _ _
    obtain ⟨htl, htc⟩ := componentTarget_exact Λ W U
    let := htl
    let := htc
    have : PreservesFiniteLimits (componentEvaluationTarget Λ W α U (a U)) := by
      dsimp only [componentEvaluationTarget]
      infer_instance
    have : PreservesFiniteColimits (componentEvaluationTarget Λ W α U (a U)) := by
      dsimp only [componentEvaluationTarget]
      infer_instance
    let : PreservesFiniteLimits (componentSourceSections Λ W U) :=
      preservesFiniteLimits_of_natIso (e U).symm
    let : PreservesFiniteColimits (componentSourceSections Λ W U) :=
      preservesFiniteColimits_of_natIso (e U).symm
    exact ⟨inferInstance, inferInstance, htl, htc, inferInstance, inferInstance,
      componentEvaluationDerivedIso Λ W α U (a U) (e U), rfl⟩

end CanonicalComparison

/-- Component pullback is evaluation on the genuine profinite component object, linearly,
naturally, and on ordinary unbounded derived objects, normalized in the pullback direction.

Source: Hemo--Richarz--Scholbach, Section 3 and Proposition 4.3(1), equation (4.2)
(blueprint: lem-sfb-component-pullback-unbounded-evaluation).

Proof for stage 3:
1. Weak contractibility splits finite qcqs covers of U: apply projectivity of its
representable sheaf to the locally surjective cover map. The affine component-site
projection and the relative component-lift pullback theorem identify its section comparison
with the fixed adjunction unit followed by restriction along the canonical lift.
2. This comparison is monoidal and invertible. Applying it to coefficient rings, followed
by alpha, gives the section-ring isomorphism. Applying it to module actions gives linearity;
the alpha and alpha-inverse coefficient changes cancel. The coefficient-factorization
clause is supplied by condensed_component_pullback_compatibility.
3. Evaluation at a w-contractible U is exact: it preserves kernels and sends epimorphisms
to surjections by weak contractibility. The comparison transfers this exactness to the
profinite evaluation. Exact component pullback and scalar restriction give the needed
exactness of the composite.
4. Apply the existing exact-derived comparison to these exact section functors and their
natural isomorphism. Its specified formula is precisely componentEvaluationDerivedIso,
so this gives the required comparison on ordinary unbounded derived categories.
5. Naturality and normalization follow from naturality of the adjunction unit and the
universal property of the relative component lift. These arguments also apply to the empty
affine test, so the comparison includes zero sections and arbitrary unbounded complexes. -/
theorem component_pullback_unbounded_evaluation
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (W : Scheme.{u}) [IsAffine W] [IsWContractibleRing Γ(W, ⊤)] :
    ∃ (_ : (componentTests W).IsContinuous
        ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
        (Scheme.ProEt.topology W)),
      ∃ (_ : (componentInverse W).Braided)
        (_ : PreservesFiniteLimits (componentInverse W))
        (_ : PreservesFiniteColimits (componentInverse W)),
        ∃ α : (componentInverse W).mapMon.obj
            (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace W))) ≅
            Mon.mk (condensedRingObj Λ.X W),
          (∃ β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
                (affineComponentSpace W) ⋙ componentInverse W ≅ upperStarFromPoint W,
            NatTrans.IsMonoidal β.hom ∧ α.hom.hom = β.hom.app Λ.X) ∧
          ComponentPullbackUnboundedEvaluation Λ W α := by
  obtain ⟨hC, _, hlim, hcol⟩ := condensed_component_inverse_image W
  let := hC
  let := componentCanonicalBraided W
  let := hlim
  let := hcol
  obtain ⟨α, hβ, _⟩ := condensed_component_pullback_compatibility Λ W
  exact ⟨hC, inferInstance, hlim, hcol, α, hβ,
    componentCanonical_evaluation Λ W α (componentSectionMap_monoidal W)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
