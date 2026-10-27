/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.VectorTraceGeometry

/-! # Exchange of vector-bundle chart source comparisons

Source: blueprint latest, sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2; local swap proof, Steps 1--2.
(blueprint: lem-pur-vector-integration-swap-chart-prefix).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
attribute [local irreducible] _root_.DerivedCategory.singleFunctors

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The two chart source comparisons differ by an invertible linear action.
Source: blueprint latest, vector-bundle purity proof paragraph 2, simultaneous
trivializations; local swap proof Steps 1--2.
(blueprint: lem-pur-vector-integration-swap-chart-prefix).

Proof: restrict the generator map of biproduct braiding to V. In the supplied frames
it gives an invertible matrix, with inverse given by the reverse braiding. After the
rank identification this matrix induces exactly the comparison of the two inverse
coordinate charts: check on each degree-one generator and use the symmetric-algebra
universal property. Its square over the identity of V is Cartesian. Paste the chart
squares with the restricted swap square. Horizontal compact-support exchange pasting
and naturality give the displayed relation between their exchange factors. The
inverse-image compositor is associative and unital; the normalized Tate pullbacks
respect composition. Thus the coefficient factors agree with precisely c, without
an additional scalar, and the constant identity comparison is affineLinearPullbackId.
The bounded/unbounded tower comparisons conjugate the remaining exchange to the
specified affineLinearTraceAction. Cancel the invertible exchange b to obtain the
formula. There is no counit or projective-line datum in this assertion. Empty opens,
rank zero (empty matrices), and the zero coefficient ring need no separate choices.
-/
theorem vectorIntegration_swap_chart_prefix (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (c : (ordinaryFinitePullback A (VectorTraceGeometry.swap S r s F G)).obj
        (vectorIntegrationCoefficient A N hA S (s + r) (VectorTraceGeometry.sum S G F)) ≅
      vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))
    (hc : c =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (VectorTraceGeometry.swap S r s F G)
        (VectorBundleZeroSection.π S (s + r) (VectorTraceGeometry.sum S G F))
        (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))
        (by simpa only [Category.comp_id] using
          (VectorTraceGeometry.swap_isPullback S r s F G).w.symm)).symm.app _ ≪≫
      (ordinaryFinitePullback A
        (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))).mapIso
        (eqToIso (congrArg (affineLinearBaseCoefficient A N hA S) (Nat.add_comm s r))))
    (b : (ordinaryFinitePullback A (𝟙 S)).obj
        (vectorIntegrationSource A N hA S (s + r) (VectorTraceGeometry.sum S G F)) ≅
      vectorIntegrationSource A N hA S (r + s) (VectorTraceGeometry.sum S F G))
    (hb : b.hom =
      (rightDerivedLowerShriekBaseChangeMap A
        (VectorTraceGeometry.swap_isPullback S r s F G)).app
        (vectorIntegrationCoefficient A N hA S (s + r) (VectorTraceGeometry.sum S G F)) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))).map c.hom)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S (r + s) (VectorTraceGeometry.sum S F G) V)
    (e' : VectorBundleZeroSection.Trivialization S (s + r) (VectorTraceGeometry.sum S G F) V) :
    letI : TopologicalSpace.NoetherianSpace V.toScheme :=
      V.ι.isOpenEmbedding.isInducing.noetherianSpace
    letI : IsNoetherian V.toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    let Q := fun d ↦ (affineTraceLeft A V.toScheme d).obj
      ((affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme))
    let B := fun (d : ℕ) (H : S.Modules) [H.IsFiniteLocallyFreeOfRank d]
      (f : VectorBundleZeroSection.Trivialization S d H V) ↦
        (rightDerivedLowerShriekBaseChangeMap A
          (vectorIntegrationChart_isPullback S d H V f)).app
            (vectorIntegrationCoefficient A N hA S d H) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (affineTraceProjection V.toScheme d)).map
            (vectorIntegrationChartCoefficient A N hA t S hS d H V f).hom ≫
        (affineLinearCompactComparison N hN A hA V.toScheme
          (affineTracePullbackInvertible N V.ι hS) d).inv
    ∃ (g : Matrix.GeneralLinearGroup (Fin (s + r)) Γ(V.toScheme, ⊤))
      (sq : IsPullback (affineTraceLinearMap V.toScheme (s + r) g)
        (affineTraceProjection V.toScheme (s + r))
        (affineTraceProjection V.toScheme (s + r)) (𝟙 V.toScheme)),
      (ordinaryFinitePullback A V.ι).map
          (b.inv ≫ (affineLinearPullbackId A S).hom.app
            (vectorIntegrationSource A N hA S (s + r) (VectorTraceGeometry.sum S G F))) ≫
        B (s + r) (VectorTraceGeometry.sum S G F) e' =
      B (r + s) (VectorTraceGeometry.sum S F G) e ≫
        eqToHom (congrArg Q (Nat.add_comm r s)) ≫
        affineLinearTraceAction N hN A hA t V.toScheme
          (affineTracePullbackInvertible N V.ι hS) (s + r)
          (affineTraceLinearMap V.toScheme (s + r) g) sq := by sorry

end AlgebraicGeometry.Etale
