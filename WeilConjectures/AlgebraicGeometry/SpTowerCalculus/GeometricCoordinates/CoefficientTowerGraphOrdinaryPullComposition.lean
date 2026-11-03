/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerGraphOrdinaryOpenSquares
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOrdinaryCompEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerOrdinaryUnitEvaluation
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Ordinary graph compositor comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option maxHeartbeats 1600000 in
-- Transporting the chosen strict and finite pullback coordinates needs this budget.
private theorem ordinaryComp_normalized (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) :
    SpTowerShriek.StrictOrdinaryCompNormalized l E b o.geometry
      o.ordinaryComp := by
  obtain ⟨c, hc⟩ := SpTowerShriek.strictOrdinaryComp l E b o.geometry
  intro X Y Z f g n M
  have he : (SpTowerShriek.ev l E X n).map ((o.ordinaryComp f g).hom.app M) =
      (SpTowerShriek.ev l E X n).map ((c f g).hom.app M) := by
    apply exact_iso_eval_injective (SpTowerShriek.ev l E X n)
      (o.ordinaryComp f g) (c f g) ?_ M
    intro K
    have h₁ := o.comp_evaluation f g n K
    have h₂ := SpTowerShriek.strictOrdinaryCompEvaluation l E b
      o.geometry c hc f g n K
    rw [o.comp_termwise f g] at h₁
    have h := (cancel_mono
      (((o.geometry (f ≫ g)).pullEvaluation n).hom.app K)).1
      (h₁.trans h₂.symm)
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp] at h
    exact (cancel_epi ((SpTowerShriek.Ev l E X n).map
      ((Functor.mapDerivedCategoryCompIso (o.geometry g).pull
        (o.geometry f).pull).inv.app K))).1 h
  rw [he]
  exact hc f g n M


/-- The right-adjoint mate of the supplied ordinary pull compositor. -/
private def ordinaryPushComp (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Y ⟶ Z) :
    (o.geometry f).push ⋙ (o.geometry h).push ≅ (o.geometry (f ≫ h)).push :=
  conjugateIsoEquiv
    ((o.geometry h).ordinaryAdjunction.comp (o.geometry f).ordinaryAdjunction)
    (o.geometry (f ≫ h)).ordinaryAdjunction (o.ordinaryComp f h).symm

/-- Finite evaluation carries this mate to the prescribed finite push compositor.
The geometric unit evaluation gives mate squares. Paste them, and conjugate the
normalized pull-compositor square to obtain the displayed right-adjoint square. -/
private theorem ordinaryPushComp_evaluation (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ) (M : SpTowerShriek.S l E X) :
    (SpTowerShriek.ev l E Z n).map ((ordinaryPushComp l E b o f h).hom.app M) ≫
        ((o.geometry (f ≫ h)).ordinaryPushEvaluation n).hom.app M =
      ((o.geometry h).ordinaryPushEvaluation n).hom.app ((o.geometry f).push.obj M) ≫
        (proEtaleConstantRingPushforward (SpTowerShriek.R l E n) h).map
          (((o.geometry f).ordinaryPushEvaluation n).hom.app M) ≫
        (proEtaleConstantRingModulePullbackComposition f h
          (SpTowerShriek.R l E n)).choose_spec.choose.hom.app
          ((SpTowerShriek.ev l E X n).obj M) := by
  have mate {A B : Scheme.{u}} (f : A ⟶ B) :
      (o.geometry f).ordinaryAdjunction.IsMateSquare
        (proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f)
        ((o.geometry f).ordinaryPullEvaluation n)
        ((o.geometry f).ordinaryPushEvaluation n) := by
    apply Adjunction.IsMateSquare.of_unit
    intro N
    simpa only [Functor.idSquareIso_hom_app, Functor.pasteSquareIso_hom_app,
      Category.id_comp] using
      SpTowerShriek.geometry_unit_evaluation l E b (o.geometry f) n N
  have hn : NatTrans.SquareCompatible
      ((o.geometry (f ≫ h)).ordinaryPullEvaluation n)
      (Functor.pasteSquareIso ((o.geometry h).ordinaryPullEvaluation n)
        ((o.geometry f).ordinaryPullEvaluation n))
      (o.ordinaryComp f h).inv
      (proEtaleConstantRingModulePullbackComposition f h
        (SpTowerShriek.R l E n)).choose.hom := by
    intro N
    have he := ordinaryComp_normalized l E b o f h n N
    have he' := congrArg (fun t ↦
      (SpTowerShriek.ev l E X n).map ((o.ordinaryComp f h).inv.app N) ≫ t ≫
        (proEtaleConstantRingModulePullbackComposition f h
          (SpTowerShriek.R l E n)).choose.hom.app
          ((SpTowerShriek.ev l E Z n).obj N)) he
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app] at he'
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at he'
    simpa only [Functor.pasteSquareIso_hom_app] using he'.symm
  have hd := NatTrans.SquareCompatible.conjugateEquiv ((mate h).comp (mate f))
    (mate (f ≫ h)) hn
  have he := hd M
  rw [← conjugateIsoEquiv_apply_hom] at he
  rw [(proEtaleConstantRingModulePullbackComposition f h
    (SpTowerShriek.R l E n)).choose_spec.choose_spec.2] at he
  simpa only [ordinaryPushComp, conjugateIsoEquiv_apply_hom,
    Functor.pasteSquareIso_hom_app, Iso.symm_hom, Category.assoc] using he

/-- The specified ordinary inverse-image compositor is preserved by graph coordinates.
Source: Local pairs and Levels, normalized ordinary units; Stacks 07A7.
(blueprint: lem-sp-graph-ordinary-pull-composition).

Proof: evaluate the derived compositor equation on degree-zero complexes and cancel
the exact single-complex comparisons to recover the normalized ordinary pull equation.
The geometric unit evaluation gives mate squares with finite coefficient pull/push.
Paste the squares and conjugate the inverse pull compositor, obtaining the normalized
ordinary push-compositor equation at every coefficient and every site object. Apply
the section pins of the presentations, their units and counits, and push_evaluation
to transport this equation to the canonical semilinear push compositor. Ordinary
sheaf-morphism extensionality identifies the two transformations. Taking conjugates
under the ordinary pull/push adjunctions gives the displayed inverse-image square.
The fixed equality of semilinear and varying-ring pull functors transports it to
moduleGComp. All cancellations use isomorphisms; zero modules and identity maps
require the same argument. -/
theorem graph_ordinary_pull_composition (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) (N : SpTowerShriek.S l E Z) :
    (g.presentation X).functor.map ((o.ordinaryComp f h).inv.app N) ≫
        (graphPullSquare l E b o g f).hom.app ((o.geometry h).pull.obj N) ≫
        (VaryingRing.pull (graphRings l E) (graphTransitions l E) f).map
          ((graphPullSquare l E b o g h).hom.app N) =
      (graphPullSquare l E b o g (f ≫ h)).hom.app N ≫
        (VaryingRing.moduleGComp (graphRings l E) (graphTransitions l E) f h).hom.app
          ((g.presentation Z).functor.obj N) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
