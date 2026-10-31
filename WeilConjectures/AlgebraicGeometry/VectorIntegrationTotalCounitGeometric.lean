/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationTotalCounitMaps
import WeilConjectures.AlgebraicGeometry.VectorIntegrationTotalCounitCoordinates
import WeilConjectures.AlgebraicGeometry.VectorIntegrationTotalCounitExchange
import WeilConjectures.AlgebraicGeometry.AffineSpaceLinearTraceInvariance

/-! # Simultaneous sum-chart trace transported to the flattened double tower

This comparison stops before the two-block adjunction normalization.
(blueprint: lem-pur-vector-integration-total-counit-geometric).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem four_assoc {C : Type*} [Category C] {W X Y Z R : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ R) :
    a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

private theorem local_trace_chart
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    [IsNoetherian V.toScheme] (e : VectorBundleZeroSection.Trivialization S d F V) :
    vectorIntegrationLocalTrace N hN A hA t D S hS d F V e =
      vectorIntegrationChartPrefix N hN A hA t S hS d F V e ≫
        affineTraceCounit A N hA t D V.toScheme
          (affineTracePullbackInvertible N V.ι hS) d := by
  unfold vectorIntegrationLocalTrace vectorIntegrationChartPrefix
  exact four_assoc _ _ _ _

private theorem finish_trace {C : Type*} [Category C] {X Y Z T R : C}
    (f : X ⟶ Y) (a : Y ⟶ Z) (e : Z ⟶ T) (b : T ⟶ T) (d : X ⟶ T)
    (q : Z ⟶ R) (q' : T ⟶ R) (hp : f ≫ a ≫ e ≫ b = d)
    (he : e ≫ q' = q) (hi : b ≫ q' = q') : f ≫ a ≫ q = d ≫ q' := by
  rw [← hp]
  simp only [Category.assoc, hi, he]

attribute [local irreducible] rightDerivedLowerShriek upperStar lowerStar
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme
  leftDerivedUpperStarComp leftDerivedUpperStarIsoMapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

/-- Transport the sum-frame local trace to the single affine trace on the flattened
s-then-r tower. No two-block adjunction counit or rightCoefficient comparison occurs.
Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, simultaneous trivializations and linear invariance.
(blueprint: lem-pur-vector-integration-total-counit-geometric).

Proof: substitute the specified coefficient and exchange witnesses. Restrict the two
frames to W and use the symmetric-algebra universal property to compare the chart
of their biproduct with the double chart followed by sumIso. On the two injections
their generator equations agree, after flattening the s-then-r tower and applying
the block permutation from F,G ordering to G,F ordering. These equations determine
the bundle morphism. Expand the local trace on the biproduct frame and paste the
inverse-coordinate squares. Compact-support exchange pasting and compositor
associativity identify the two chart exchanges with chartPrefix followed by the
compact-support compositor on the two affine projections. Inverse-image
associativity identifies the coefficient comparison; naturality pulls the base
Tate comparison through the exchange. In the resulting affine trace the only
extra factor is the action of the displayed coordinate permutation. Linear trace
invariance cancels that action. The remaining inverse-flattening exchange, total
coefficient descent and rank-(s+r) counit are exactly flattenedTrace. This proof
does not identify that single trace with a block counit. At zero rank the empty
block permutation, identity chart and compositor unit give the same calculation;
an empty W causes no additional restriction. -/
theorem vectorIntegration_totalCounit_geometric (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (V U : S.Opens) (eF : VectorBundleZeroSection.Trivialization S r F V)
    (eG : VectorBundleZeroSection.Trivialization S s G U)
    (W : S.Opens) [IsNoetherian W.toScheme] (hWV : W ≤ V) (hWU : W ≤ U) :
    letI := affineTraceNoetherian W.toScheme s
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
    ∀ (c : (ordinaryFinitePullback A (VectorTraceGeometry.sumIso S r s F G).hom).obj
        (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G)) ≅ Wh)
      (hc : c =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (VectorTraceGeometry.sumIso S r s F G).hom
      (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))
      (h)
      (by simpa only [Category.comp_id] using
        (VectorTraceGeometry.sumIso_isPullback S r s F G).w.symm)).symm.app _),
    ∀ (ex : (ordinaryFinitePullback A (𝟙 S)).obj
        (vectorIntegrationSource A N hA S (r + s) (VectorTraceGeometry.sum S F G)) ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).obj
        ((ordinaryFinitePullback A (VectorTraceGeometry.sumIso S r s F G).hom).obj
          (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))))
      (hex : ex = (by
      have hex := (unboundedEtaleCompactSupport_baseChange A
        (VectorTraceGeometry.sumIso_isPullback S r s F G)).1
      have hexa := @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hex
        (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))
      exact (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 S)).app _ ≪≫
        @asIso _ _ _ _ ((unboundedEtaleCompactSupportBaseChange A
          (VectorTraceGeometry.sumIso_isPullback S r s F G)).app
          (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G)))
          hexa ≪≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
            (VectorTraceGeometry.sumIso S r s F G).hom).symm.app _))),
    let kh :=
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (h)).map
        (c).inv ≫
      (ex).inv ≫
      (affineLinearPullbackId A S).hom.app _;
    (ordinaryFinitePullback A W.ι).map
      ((unboundedEtaleLowerShriekCompIso A (q)
        (VectorBundleZeroSection.π S s G)).hom.app
        (Wh) ≫
      kh) ≫
      vectorIntegrationLocalTrace N hN A hA t D S hS (r + s)
        (VectorTraceGeometry.sum S F G) W
        (VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU) =
    VectorIntegrationTotalCounit.chartPrefix A N hA t S hS r s F G V U eF eG
      W hWV hWU ≫
      (unboundedEtaleLowerShriekCompIso A
        (affineTraceProjection (affineTraceTower W.toScheme s) r)
        (affineTraceProjection W.toScheme s)).hom.app _ ≫
      VectorIntegrationTotalCounit.flattenedTrace N hN A hA t D W.toScheme
        (affineTracePullbackInvertible N W.ι hS) r s := by
  let := affineTraceNoetherian W.toScheme s
  dsimp only
  intro c hc ex hex
  obtain ⟨g, hg⟩ := vectorIntegration_totalCounit_coordinates S r s F G V U eF eG W hWV hWU
  have hp := vectorIntegration_totalCounit_exchange N hN A hA t S hS r s F G V U eF eG
    W hWV hWU c hc ex hex g hg
  obtain ⟨sq, hi⟩ := affineSpaceLinearTraceInvariance N hN A hA t D W.toScheme
    (affineTracePullbackInvertible N W.ι hS) (s + r) g
  have hs : sq = affineTraceLinearMap_isPullback W.toScheme (s + r) g :=
    Subsingleton.elim _ _
  subst sq
  have he (d d' : ℕ) (h : d = d') :
      eqToHom (congrArg (fun n ↦ (affineTraceLeft A W.toScheme n).obj
        ((affineTraceRight A N hA W.toScheme n).obj (ordinaryFiniteUnit A W.toScheme))) h) ≫
        affineTraceCounit A N hA t D W.toScheme
          (affineTracePullbackInvertible N W.ι hS) d' =
      affineTraceCounit A N hA t D W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d := by
    subst d'
    simp only [eqToHom_refl, Category.id_comp]
  dsimp only at hp
  have h := finish_trace _ _ _ _ _ _ _ hp (he _ _ (Nat.add_comm r s)) hi
  rw [local_trace_chart N hN A hA t D S hS (r + s)
    (VectorTraceGeometry.sum S F G) W
    (VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU)]
  simpa only [VectorIntegrationTotalCounit.flattenedTrace, Category.assoc] using h

end AlgebraicGeometry.Etale
