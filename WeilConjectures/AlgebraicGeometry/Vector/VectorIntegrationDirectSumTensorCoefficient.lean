/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianTensorDescent

import all Mathlib.Logic.Small.Defs

/-! # Ordered coefficient transport on a double chart

Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, simultaneous trivializations and ordered affine counits.
(blueprint: lem-pur-vector-integration-direct-sum-tensor-coefficient).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] rightDerivedLowerShriek upperStar
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme leftDerivedUpperStarComp
  leftDerivedUpperStarIsoMapDerivedCategory
attribute [local implicit_reducible] Scheme.Modules

/-- Ordered coefficient transport on a double chart.
Source: blueprint vector-bundle purity proof, paragraph 2.
(blueprint: lem-pur-vector-integration-direct-sum-tensor-coefficient).

Proof:
1. Use Iso.comp_inv_eq for the constructed Cartesian descent e, so the goal is
chart*(d.hom)=reference.coefficient.hom followed by e.hom. Substitute hd. Expand coefficient,
rightCoefficient and e, but keep coefficientDescent, derived tensor and base-coefficient pullback
abstract. The inverse inner coefficientDescent at the end of rightCoefficient inverse cancels the
identical forward coefficientDescent at the beginning of e.

2. Apply monoidality of inverse-image composition to the explicit decomposition d. Tensor-
comparison naturality cancels the termwise-versus-derived exact comparison introduced by hd
against its inverse in e. Apply square_tensor_inverse to the inner square and square_paste to that
square above the G square (both are proved helpers in
VectorIntegrationRestrictedChartCoefficientCore). This leaves one equation for each ordered Tate
factor.

3. Write b_j(n) for vectorIntegrationBaseCoefficientPullback along j. The rank-r equation is
g*(b_p(r).hom) followed by b_g(r).hom = S_G inverse at P_S(r), followed by qs*(b_Wι(r).hom) and
b_qs(r).hom. Derive it by applying vectorIntegrationBaseCoefficientPullback_comp to the two
composites g≫p and qs≫W.ι, which agree by the outer square, and cancelling the pullback
compositor. For rank s expand cG = S_G inverse at P_S(s), followed by qs*b_Wι(s) and inverse
affine coefficient descent; its inverse cancels the rank-s descent occurring in rightCoefficient.
Tensor naturality combines these two equations.

4. Apply vectorIntegrationBaseCoefficientPullback_add to the ordered ranks s and r and the open
inclusion W→S. Its independent induction has been proved in the companion module
VectorIntegrationBaseCoefficientAdd; no copy of the surrounding model-orientation module is
imported.

5. Use the power-add equation of the preceding step to identify the remaining total coefficient.
Move the eqToIso from r+s=s+r across the normalized pullback by equality induction on its index;
this requires no commutativity of the ordered tensor factors. Compose with e inverse to recover
the stated equality. Neither integration nor a counit occurs. All constructions include rank zero,
empty schemes and zero rings.
-/
theorem vectorIntegrationDirectSumTensorCoefficient (N : ℕ)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (V U : S.Opens) (eF : VectorBundleZeroSection.Trivialization S r F V)
    (eG : VectorBundleZeroSection.Trivialization S s G U)
    (W : S.Opens) [IsNoetherian W.toScheme] (hWV : W ≤ V) (hWU : W ≤ U) :
    let fibre :=
      (Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F;
    let q :=
      VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
      (fibre);
    let h :=
      q ≫ VectorBundleZeroSection.π S s G;
    let Wh :=
      (ordinaryFinitePullback A (h)).obj
      (affineLinearBaseCoefficient A N hA S (r + s));
    ∀ (d : Wh ≅
      ((ordinaryFiniteTensor A _).obj
        ((upperStar (ModuleCat.{u + 1} A) q).mapDerivedCategory.obj
          (vectorIntegrationCoefficient A N hA S s G))).obj
        (vectorIntegrationCoefficient A N hA (VectorBundleZeroSection.scheme S s G) r fibre))
      (hd : d =
      (ordinaryFinitePullback A (h)).mapIso
        (eqToIso (congrArg (affineLinearBaseCoefficient A N hA S) (Nat.add_comm r s)) ≪≫
          WeilConjectures.PurityFiniteSetting.purityPowerAdd A N hA S s r) ≪≫
      ordinaryFiniteTensorPullback A (h)
        (affineLinearBaseCoefficient A N hA S s) (affineLinearBaseCoefficient A N hA S r) ≪≫
      ordinaryFiniteTensorRightMapIso A _
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (q)
          (VectorBundleZeroSection.π S s G)).app _ ≪≫
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
            (q)).app (vectorIntegrationCoefficient A N hA S s G))
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (q)
          (VectorBundleZeroSection.π S s G)).app _ ≪≫
          (ordinaryFinitePullback A (q)).mapIso
            (vectorIntegrationBaseCoefficientPullback A N hA t
              (VectorBundleZeroSection.π S s G) hS r))),
    let E := VectorBundleZeroSection.scheme S s G
    let p := VectorBundleZeroSection.π S s G
    let g := vectorIntegrationRestrictedChart S s G W U hWU eG
    let B := affineTraceTower W.toScheme s
    let hW := affineTracePullbackInvertible N W.ι hS
    let hB := affineTracePullbackInvertible N g (affineTracePullbackInvertible N p hS)
    let cG := vectorIntegrationCartesianCoefficient A N hA t p W.ι hW s g
      (vectorIntegrationRestrictedChart_isPullback S s G W U hWU eG)
      (affineLinearBaseCoefficient A N hA S s)
      (vectorIntegrationBaseCoefficientPullback A N hA t W.ι hS s)
    (ordinaryFinitePullback A
        (VectorIntegrationDirectSumCounit.chart S r s F G V U eF eG W hWV hWU)).map d.hom ≫
      (vectorIntegrationCartesianTensorDescent A N hA t q g hB r
        (VectorIntegrationDirectSumCounit.chart S r s F G V U eF eG W hWV hWU)
        (VectorIntegrationDirectSumCounit.chart_isPullback S r s F G V U eF eG W hWV hWU)
        (affineLinearBaseCoefficient A N hA E r)
        (vectorIntegrationCoefficient A N hA S s G)
        ((affineTraceRight A N hA W.toScheme s).obj (ordinaryFiniteUnit A W.toScheme)) cG
        (vectorIntegrationBaseCoefficientPullback A N hA t g
          (affineTracePullbackInvertible N p hS) r)).inv =
        (VectorIntegrationDirectSumCounit.coefficient N A hA t S hS r s F G V U eF eG
          W hWV hWU).hom := by
  sorry

end AlgebraicGeometry.Etale
