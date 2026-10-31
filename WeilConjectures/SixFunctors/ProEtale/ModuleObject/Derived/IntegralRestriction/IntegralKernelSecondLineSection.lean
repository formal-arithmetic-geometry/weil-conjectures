/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelTateComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
import all WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
import all WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateSection

import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Restricting the integral Tate comparison to the diagonal -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients RationalP1
set_option allowUnsafeReducibility true in
attribute [local reducible] traceTate
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

attribute [local instance 40000] moduleObjectDerivedPullbackCommShift

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp

set_option maxHeartbeats 800000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
private theorem integralLinePull_comp {X S R : Scheme.{u}} (f : X ⟶ S) (g : S ⟶ R)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ x : S, Invertible (ℓ : S.residueField x)]
    [∀ x : R, Invertible (ℓ : R.residueField x)] :
    (CondensedRing.upperStarComp (Profinite.padicIntegersRingObj ℓ E.val) f g).hom.app
        (spIntegralTwist R ℓ E) ≫
      (CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E.val) f).map
        (integralLinePullIso ℓ E g).hom ≫ (integralLinePullIso ℓ E f).hom =
      (integralLinePullIso ℓ E (f ≫ g)).hom := by
  exact module_comparison_comp (Profinite.padicIntegersRingObj ℓ E.val) f g
    (spIntegralTwist R ℓ E) (spIntegralTwist S ℓ E) (spIntegralTwist X ℓ E)
    (spIntegralComparison g ℓ E) (spIntegralComparison f ℓ E)
    (spIntegralComparison (f ≫ g) ℓ E)
    (integralLinePullIso ℓ E g).hom (integralLinePullIso ℓ E f).hom
    (integralLinePullIso ℓ E (f ≫ g)).hom
    (linePull_adjunct _ g _ _ _ _) (linePull_adjunct _ f _ _ _ _)
    (linePull_adjunct _ (f ≫ g) _ _ _ _) (integral_comp ℓ E f g)

private def integralDerivedLine {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ x : S, Invertible (ℓ : S.residueField x)] :=
  nativeComparison (Profinite.padicIntegersRingObj ℓ E.val) f
    (spIntegralTwist S ℓ E) (spIntegralTwist X ℓ E) (integralLinePullIso ℓ E f)

set_option maxHeartbeats 800000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
private theorem integralDerivedLine_hom {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ x : S, Invertible (ℓ : S.residueField x)] :
    (((CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E.val)
      f).singleFunctorCompLeftDerivedFunctorIso.app (spIntegralTwist S ℓ E)) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (integralLinePullIso ℓ E f)).hom =
      (integralDerivedLine ℓ E f).hom := by
  rfl

set_option maxHeartbeats 3200000 in
-- Check the unshifted normalized comparison separately from its shifted equation.
private theorem integralDerivedLine_comp {X S R : Scheme.{u}} (f : X ⟶ S) (g : S ⟶ R)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ x : S, Invertible (ℓ : S.residueField x)]
    [∀ x : R, Invertible (ℓ : R.residueField x)] :
    (modulePullbackDerivedCompositor (Profinite.padicIntegersRingObj ℓ E.val) f g).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj (spIntegralTwist R ℓ E)) ≫
      (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) f).map
        (integralDerivedLine ℓ E g).hom ≫ (integralDerivedLine ℓ E f).hom =
      (integralDerivedLine ℓ E (f ≫ g)).hom := by
  exact nativeComparison_comp (Profinite.padicIntegersRingObj ℓ E.val) f g
    (spIntegralTwist R ℓ E) (spIntegralTwist S ℓ E) (spIntegralTwist X ℓ E)
    (integralLinePullIso ℓ E g) (integralLinePullIso ℓ E f)
    (integralLinePullIso ℓ E (f ≫ g)) (integralLinePull_comp ℓ E f g)

attribute [local irreducible] integralDerivedLine

set_option maxHeartbeats 3200000 in
-- Check the shifted equation with the native commutation structures fixed.
private theorem integralShiftedLine_comp {X S R : Scheme.{u}} (f : X ⟶ S) (g : S ⟶ R)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ x : S, Invertible (ℓ : S.residueField x)]
    [∀ x : R, Invertible (ℓ : R.residueField x)] :
    (modulePullbackDerivedCompositor (Profinite.padicIntegersRingObj ℓ E.val) f g).hom.app
        (traceTate ℓ E R) ≫
      (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) f).map
        (integralShiftedLinePullIso ℓ E g).hom ≫
      (integralShiftedLinePullIso ℓ E f).hom =
      (integralShiftedLinePullIso ℓ E (f ≫ g)).hom := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let hc : NatTrans.CommShift (modulePullbackDerivedCompositor Λ f g).hom ℤ :=
    nativeCompositor_sourceShift Λ f g
  unfold integralShiftedLinePullIso
  simp only [id, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  erw [integralDerivedLine_hom ℓ E g, integralDerivedLine_hom ℓ E f,
    integralDerivedLine_hom ℓ E (f ≫ g)]
  apply shifted_comparison_comp
  exact integralDerivedLine_comp ℓ E f g

set_option maxHeartbeats 800000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
private theorem integralShiftedLine_congr {X S : Scheme.{u}}
    (f g : X ⟶ S) (h : f = g)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ x : S, Invertible (ℓ : S.residueField x)] :
    (integralShiftedLinePullIso ℓ E f).hom =
      eqToHom (congrArg (fun k ↦
        (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) k).obj
          (traceTate ℓ E S)) h) ≫ (integralShiftedLinePullIso ℓ E g).hom := by
  subst g
  simp only [eqToHom_refl, Category.id_comp]

set_option maxHeartbeats 800000 in
-- Keep the fixed native derived comparisons folded during elaboration.
/-- Integral Cartesian Tate comparisons restrict to the canonical section comparison.
Source: the integral projective-line triangle calculation, paragraph (1), and the
root-normalized coefficient comparison.
(blueprint: lem-integral-kernel-second-line-section).
Proof: the finite root maps commute with inverse-image composition. Their integral
limit does too. The scalar-extension adjunction transfers this equation to module
pullback. Applying the single functor, its derived comparison and shift by two
preserves composition. The composition equation for the identity forces its line
comparison to be the identity compositor. Apply the composition equation to the
section followed by f and cancel the compositor. This is the canonical section map. -/
theorem integralKernel_second_line_section (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val)
        (diagonalImmersion Y)).map (integralShiftedLinePullIso ℓ E f).hom ≫
      (integralShiftedLinePullIso ℓ E (diagonalImmersion Y)).hom =
      (pullSectionIso (Profinite.padicIntegersRingObj ℓ E.val) Y f h).hom.app
        (traceTate ℓ E (ProjectiveLine Y)) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let P := ProjectiveLine Y
  let B := traceTate ℓ E P
  have hi : (integralShiftedLinePullIso ℓ E (𝟙 P)).hom =
      (nativeIdentity Λ P).hom.app B := by
    let F := moduleObjectDerivedPullback Λ (𝟙 P)
    have hf : F.Faithful := Functor.Faithful.of_iso (nativeIdentity Λ P).symm
    apply F.map_injective
    apply (cancel_epi
      ((modulePullbackDerivedCompositor Λ (𝟙 P) (𝟙 P)).hom.app B)).mp
    have hc := integralShiftedLine_comp ℓ E (𝟙 P) (𝟙 P)
    have hu := leftDerivedUpperStarComp_id_right_app Λ (𝟙 P) B
    rw [integralShiftedLine_congr ℓ E ((𝟙 P) ≫ 𝟙 P) (𝟙 P)
      (Category.id_comp _)] at hc
    have hh : (modulePullbackDerivedCompositor Λ (𝟙 P) (𝟙 P)).hom.app B ≫
        F.map (integralShiftedLinePullIso ℓ E (𝟙 P)).hom =
      eqToHom (by rw [Category.id_comp]) := by
      apply (cancel_mono (integralShiftedLinePullIso ℓ E (𝟙 P)).hom).mp
      simpa only [Category.assoc] using hc
    exact hh.trans hu.symm
  have hc := integralShiftedLine_comp ℓ E (diagonalImmersion Y) f
  rw [integralShiftedLine_congr ℓ E (diagonalImmersion Y ≫ f) (𝟙 P) h, hi] at hc
  apply (cancel_epi
    ((modulePullbackDerivedCompositor Λ (diagonalImmersion Y) f).hom.app B)).mp
  rw [hc]
  dsimp only [Λ, P, B] at *
  simp only [pullSectionIso_eq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    nativeIdentity, modulePullbackDerivedCompositor]
  erw [Iso.hom_inv_id_app_assoc]
  conv_rhs => erw [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  rfl
end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
