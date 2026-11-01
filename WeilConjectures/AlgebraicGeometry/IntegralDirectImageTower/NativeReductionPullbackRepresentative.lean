/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import all WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerDerivedPullback
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.NativeReductionOrdinaryComposition
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.NativeReductionDerivedPasting

/-! # Composition on flat-term K-flat representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.TwoSquare
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open SheafOfModules
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
set_option synthInstance.maxHeartbeats 200000 in
-- Resolve instances across the equivalent integral and section-module presentations.
set_option maxHeartbeats 1600000 in
-- Cancel the comparison across the integral and strict-system derived models.
/-- The pasted comparison agrees with the composite comparison on flat-term K-flat
representatives. The hypotheses are precisely the independent-coefficient K-flatness
and termwise flatness hypotheses of `ReductionPull.representatives`.
Source: normalized scalar/pullback construction, paragraphs (2)--(3).
(blueprint: lem-dla1-native-reduction-proper-composition-representative).
The proof composes the two representative equations of `q.pullback g` and
`q.pullback f`, using naturality of the reduction counit and the termwise system
compositor formula. Geometric inverse image preserves the resolving class, so the
second representatives equation applies to the pulled-back complex. The ordinary
comparison is identified by its tensor-generator normalization. Invert and reassociate
the resulting representatives equation to obtain the displayed identity. This calculation
only concerns the stated resolving class; extension to arbitrary derived objects is
proved separately in `nativeReductionPullbackComposition_component`.
-/
theorem nativeReductionPullbackComposition_representative (s : Presentation l E)
    (q : ReductionGeometry l E s) :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (P : CochainComplex (Modules l E Z) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (R := spIntegralSectionRing l E Z)
        (((spIntegralModuleEquivalence l E Z).functor.mapHomologicalComplex (.up ℤ)).obj P) →
      (∀ i : ℤ, IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := Scheme.ProEt.topology Z)
        (R := spIntegralSectionRing l E Z)
        ((spIntegralModuleEquivalence l E Z).functor.obj (P.X i))) →
      (((((TwoSquare.mk _ _ _ _ (q.pullback g).derived.inv) ≫ᵥ
        (TwoSquare.mk _ _ _ _ (q.pullback f).derived.inv)).whiskerRight
          (s.operations.comp f g).inv).whiskerLeft
            (CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) f g).inv).natTrans.app
              (DerivedCategory.Q.obj P)) =
        ((TwoSquare.mk _ _ _ _ (q.pullback (f ≫ g)).derived.inv).natTrans.app
          (DerivedCategory.Q.obj P)) := by
  intro X Y Z f g P hP hflat
  let d := nativeReductionDerivedPaste l E s q f g
  have := reduction_comparison_isIso l E s Z P hP
  have hd : d.hom.app (DerivedCategory.Q.obj P) =
      (q.pullback (f ≫ g)).derived.hom.app (DerivedCategory.Q.obj P) := by
    apply (cancel_mono
      ((SpTowerShriek.pull l E s.base (s.operations.geometry (f ≫ g))).map
          (reductionComplexComparison l E s Z P) ≫
        (s.operations.geometry (f ≫ g)).pull.mapDerivedCategoryFactors.hom.app
          (((ordinaryReduction l E s Z).mapHomologicalComplex (.up ℤ)).obj P))).1
    have h := nativeReductionDerivedPaste_normalized l E s q f g P hP hflat
    rw [nativeReductionOrdinaryPaste_eq l E s q f g] at h
    exact h.trans ((q.pullback (f ≫ g)).representatives P hP hflat).symm
  have hi := congrArg
    (fun t ↦ d.inv.app (DerivedCategory.Q.obj P) ≫ t ≫
      (q.pullback (f ≫ g)).derived.inv.app (DerivedCategory.Q.obj P)) hd
  simp only [Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id] at hi
  simpa only [d, nativeReductionDerivedPaste, pull,
    CondensedRing.moduleObjectDerivedPullback, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_inv, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, TwoSquare.vComp_app, TwoSquare.whiskerLeft_app,
    TwoSquare.whiskerRight_app, TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using hi.symm
end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
