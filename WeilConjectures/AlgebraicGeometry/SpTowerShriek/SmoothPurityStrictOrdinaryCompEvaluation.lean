/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOrdinaryComp
import all WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleComparisonLocalization

/-! # Evaluation of ordinary strict geometric compositors

Source: blueprint operations proof (2), localized inverse-image composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

/-- The ordinary normalized equation descends to the unbounded derived categories.
Source: blueprint operations proof (2); Stacks 05RU, 07A4 and 0D6D.
(blueprint: lem-sp-strict-ordinary-compositor-evaluation).

Proof: cancel the ordinary compositor and the canonical module compositor in
the normalization hcomp; this is the forward ordinary square equation with
cF = (ordinaryComp f g).symm and cG the canonical module compositor. Apply
Functor.mapDerivedCategorySquareIso_comp to the three ordinary pullback
evaluation squares (blueprint: lem-pod-derived-exact-square-composition). The
helper pull_evaluation_model of TowerOpenAdjunctionEvaluation, which transports
the generic pullEvaluation_model through the HEq fields of each geometry,
identifies every localized square with the specified pullEvaluation. The
published module-localization theorem
proEtaleConstantRingPullbackComposition_eq_mapModuleComparison identifies the
localized module compositor with proEtaleConstantRingPullbackComposition. Take
the component at K of the resulting equality of natural isomorphisms, precompose
with the evaluation of the localized ordinary compositor and postcompose with the
finite compositor, and cancel the isomorphisms. Zero complexes, n = 0 and empty
schemes are included; quotient flatness and boundedness are never invoked. -/
theorem strictOrdinaryCompEvaluation (b : Base l E)
    (geometry : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Geometry l E b f)
    (ordinaryComp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      (geometry g).pull ⋙ (geometry f).pull ≅ (geometry (f ≫ g)).pull)
    (hcomp : StrictOrdinaryCompNormalized l E b geometry ordinaryComp) :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (K : D l E Z),
      (Ev l E X n).map
          (((Functor.mapDerivedCategoryCompIso (geometry g).pull (geometry f).pull).symm ≪≫
            Functor.mapDerivedCategoryNatIso (ordinaryComp f g)).hom.app K) ≫
          ((geometry (f ≫ g)).pullEvaluation n).hom.app K =
        ((geometry f).pullEvaluation n).hom.app ((pull l E b (geometry g)).obj K) ≫
          (proEtaleConstantRingDerivedPullback (R l E n) f).map
            (((geometry g).pullEvaluation n).hom.app K) ≫
          (proEtaleConstantRingPullbackComposition f g (R l E n)).hom.app
            ((Ev l E Z n).obj K) := by
  intro X Y Z f g n K
  let : Finite (R l E n) := b.finite n
  have ho (M : S l E Z) :
      (ev l E X n).map ((ordinaryComp f g).inv.app M) ≫
          ((geometry f).ordinaryPullEvaluation n).hom.app ((geometry g).pull.obj M) ≫
          (proEtaleConstantRingPullback (R l E n) f).map
            (((geometry g).ordinaryPullEvaluation n).hom.app M) =
        ((geometry (f ≫ g)).ordinaryPullEvaluation n).hom.app M ≫
          (proEtaleConstantRingModulePullbackComposition f g (R l E n)).choose.hom.app
            ((ev l E Z n).obj M) := by
    have h := congrArg (fun t ↦
      (ev l E X n).map ((ordinaryComp f g).inv.app M) ≫ t ≫
        (proEtaleConstantRingModulePullbackComposition f g (R l E n)).choose.hom.app
          ((ev l E Z n).obj M)) (hcomp f g n M)
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app] at h
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
    exact h.symm
  have hd := Functor.mapDerivedCategorySquareIso_comp
    (geometry g).pull (geometry f).pull (geometry (f ≫ g)).pull
    (proEtaleConstantRingPullback (R l E n) g)
    (proEtaleConstantRingPullback (R l E n) f)
    (proEtaleConstantRingPullback (R l E n) (f ≫ g))
    (ev l E Z n) (ev l E Y n) (ev l E X n)
    ((geometry g).ordinaryPullEvaluation n) ((geometry f).ordinaryPullEvaluation n)
    ((geometry (f ≫ g)).ordinaryPullEvaluation n) (ordinaryComp f g).symm
    (proEtaleConstantRingModulePullbackComposition f g (R l E n)).choose ho
  simp only [← pull_evaluation_model l E b] at hd
  rw [← proEtaleConstantRingPullbackComposition_eq_mapModuleComparison] at hd
  let c := (Functor.mapDerivedCategoryCompIso (geometry g).pull (geometry f).pull).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryComp f g)
  have hc : Functor.mapDerivedCategoryNatIso (ordinaryComp f g).symm ≪≫
      Functor.mapDerivedCategoryCompIso (geometry g).pull (geometry f).pull = c.symm := by
    apply Iso.ext
    simp only [c, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm]
  rw [hc] at hd
  have hm := NatTrans.congr_app (congrArg Iso.hom hd) K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id] at hm
  have h := congrArg (fun t ↦ (Ev l E X n).map (c.hom.app K) ≫ t ≫
    (proEtaleConstantRingPullbackComposition f g (R l E n)).hom.app
      ((Ev l E Z n).obj K)) hm
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
  exact h.symm

end AlgebraicGeometry.ProEtale.SpTowerShriek
