/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # Higher vanishing from the specified affine-line unit

Source: Step 1 of the relative Kummer proof: the unit is an isomorphism, hence the
higher direct images vanish (blueprint: lem-pur-relative-kummer-unit-vanishing).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- A direct image identified by its unit with a degree-zero coefficient sheaf has no
nonzero-degree cohomology. Source: relative Kummer proof, Step 1
(blueprint: lem-pur-relative-kummer-unit-vanishing). -/
theorem isZero_homology_of_relativeUnit_isIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool)
    (hi : IsIso (P.relativeUnit h f twisted)) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.obj
        (P.derivedSheaf h X twisted))) := by
  have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (P.derivedSheaf h Y twisted)) := by
    unfold derivedSheaf
    by_cases hn : q < 0
    · exact DerivedCategory.isZero_of_isGE _ 0 q hn
    · exact DerivedCategory.isZero_of_isLE _ 0 q (by omega)
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    (asIso (P.relativeUnit h f twisted))).symm

/-- Complete clauses (1)-(3) from the specified maps: affine higher vanishing follows
from the twisted affine unit and is not a separate assumption.
Source: relative Kummer proof, Steps 1 and 2
(blueprint: lem-pur-relative-kummer-unit-vanishing). -/
theorem relativeKummerConclusions_of_maps (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (hu : IsIso (P.relativeUnit h (lineProjection Y) false))
    (ht : IsIso (P.relativeUnit h (lineProjection Y) true))
    (hzero : IsIso ((DerivedCategory.homologyFunctor _ 0).map
      (P.relativeUnit h (puncturedProjection Y) true)))
    (hgen : IsIso (P.kummerGenerator h Y a))
    (hvan : ∀ (m : ℕ), 2 ≤ m → IsZero
      ((DerivedCategory.homologyFunctor _ (m : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.derivedSheaf h (Punctured Y) true)))) :
    P.RelativeKummerConclusions h Y a := by
  refine ⟨hu, ht, ?_, hzero, hgen, hvan⟩
  intro m hm
  exact P.isZero_homology_of_relativeUnit_isIso h (lineProjection Y) true ht m
    (by omega)

/-- Negative direct images of a degree-zero coefficient object vanish over any base.
Source: the connective bound used in the cohomological criterion of Step 3
(blueprint: lem-pur-relative-kummer-unit-vanishing). -/
theorem isZero_negative_relativeImage (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (twisted : Bool) (q : ℤ) (hq : q < 0) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.obj
        (P.derivedSheaf h X twisted))) := by
  let M : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
    ⟨P.derivedSheaf h X twisted, ⟨0, by unfold derivedSheaf; infer_instance⟩⟩
  have hM : (P.derivedSheaf h X twisted).IsGE 0 := by
    unfold derivedSheaf
    infer_instance
  have : M.IsGE 0 := (M.isGE_ι_obj_iff 0).1 hM
  let F := ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f
  exact (F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE M 0 hq).of_iso
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) q).mapIso
      (F.rightDerivedFunctorPlusCompatibility.app M)).symm

/-- The natural-number vanishing in the relative conclusion and connectiveness give
exactly the integral-degree bound required by the exchange-generators criterion.
Source: relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-unit-vanishing). -/
theorem isZero_puncturedImage_of_relative_conclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (B : Scheme.{u})
    (a : B ⟶ Spec (CommRingCat.of P.field.k))
    (hc : P.RelativeKummerConclusions h B a) (q : ℤ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection B)).rightDerivedFunctor.obj
          (P.derivedSheaf h (Punctured B) true))) := by
  by_cases hn : q < 0
  · exact P.isZero_negative_relativeImage h (puncturedProjection B) true q hn
  · obtain ⟨_, _, _, _, _, hv⟩ := hc
    have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
    simpa only [he] using hv q.toNat (by omega)

end WeilConjectures.PurityFiniteSetting
