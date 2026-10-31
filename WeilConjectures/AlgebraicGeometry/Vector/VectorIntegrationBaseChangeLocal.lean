/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseChangeLocalUnit

/-! # Base change on two vector-bundle frame opens

Source: blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-vector-integration-base-change-local).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The exchange equation on a common refinement of two frame opens.
Only the restrictions of the two input arrows on the supplied frames are prescribed;
neither arrow is required to be a global integration or globally normalized.
Source: blueprint vector-bundle purity proof, paragraph 2, arbitrary base change,
specified affine counits and independence of the frame; geometric-descent Step 3.
(blueprint: lem-pur-vector-integration-base-change-local).

Proof: restrict the source frame on V along g and the target frame on U along a.
The symmetric-algebra generator formula for baseChange identifies the resulting
Cartesian bundle with the base change of the source coordinate bundle. The two
frames over W differ by an invertible linear substitution. Paste the compact-support
exchange squares for j, f and the inverse charts, using j = a followed by U.ι and
j followed by f = g followed by V.ι. Their pasting equation, together with Tate
pullback composition, identifies the source comparison with the specified b and c.
Substitute the two supplied single-frame equations. The affine-space counit
base-change equation gives equality for the pulled-back source frame; linear trace
invariance gives equality for the target frame. Naturality of the inverse-image
compositors and the constant-unit composition equation identify the remaining
outer factors. Cancel the constant-unit comparison over W to obtain the displayed
unadjusted restriction equation. This calculation involves only these two frames,
not a covering or a global gluing assertion. Empty W, rank zero and the zero ring
satisfy the same unit and exchange equations.
-/
theorem vectorIntegration_baseChange_local (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r]
    (c : (ordinaryFinitePullback A (VectorTraceGeometry.baseChange f r F)).obj
        (vectorIntegrationCoefficient A N hA S r F) ≅
      vectorIntegrationCoefficient A N hA T r ((Scheme.Modules.tensorPullback f).obj F))
    (hc : c =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (VectorTraceGeometry.baseChange f r F) (VectorBundleZeroSection.π S r F)).symm.app _ ≪≫
      (eqToIso (congrArg (ordinaryFinitePullback A)
        (VectorTraceGeometry.baseChange_isPullback f r F).w)).app _ ≪≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F)) f).app _ ≪≫
      (ordinaryFinitePullback A
        (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F))).mapIso
        (vectorIntegrationBaseCoefficientPullback A N hA t f hS r))
    (b : (ordinaryFinitePullback A f).obj (vectorIntegrationSource A N hA S r F) ≅
      vectorIntegrationSource A N hA T r ((Scheme.Modules.tensorPullback f).obj F))
    (hb : b.hom =
      (rightDerivedLowerShriekBaseChangeMap A
        (VectorTraceGeometry.baseChange_isPullback f r F)).app
        (vectorIntegrationCoefficient A N hA S r F) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F))).map c.hom)
    (D : ∀ (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (N : Γ(X, ⊤))),
      OrdinaryFiniteP1Datum A N hA t X hX)
    (V : S.Opens) (eS : VectorBundleZeroSection.Trivialization S r F V)
    (U : T.Opens)
    (eT : VectorBundleZeroSection.Trivialization T r
      ((Scheme.Modules.tensorPullback f).obj F) U)
    (W : Scheme.{u}) [IsNoetherian W]
    (j : W ⟶ T) (a : W ⟶ U.toScheme) (g : W ⟶ V.toScheme)
    (ha : a ≫ U.ι = j) (hg : j ≫ f = g ≫ V.ι)
    (kS : vectorIntegrationSource A N hA S r F ⟶ ordinaryFiniteUnit A S)
    (kT : vectorIntegrationSource A N hA T r ((Scheme.Modules.tensorPullback f).obj F) ⟶
      ordinaryFiniteUnit A T)
    (hkS : (ordinaryFinitePullback A V.ι).map kS ≫ (ordinaryFiniteUnitPullback A V.ι).hom =
      vectorIntegrationLocalTrace N hN A hA t D S hS r F V eS)
    (hkT : (ordinaryFinitePullback A U.ι).map kT ≫ (ordinaryFiniteUnitPullback A U.ι).hom =
      vectorIntegrationLocalTrace N hN A hA t D T (affineTracePullbackInvertible N f hS) r
        ((Scheme.Modules.tensorPullback f).obj F) U eT) :
    (ordinaryFinitePullback A j).map (b.hom ≫ kT) =
      (ordinaryFinitePullback A j).map
        ((ordinaryFinitePullback A f).map kS ≫ (ordinaryFiniteUnitPullback A f).hom) := by
  apply (cancel_mono (ordinaryFiniteUnitPullback A j).hom).mp
  exact vectorIntegration_baseChange_local_unit N hN A hA t f hS r F c hc b hb D
    V eS U eT W j a g ha hg kS kT hkS hkT

end AlgebraicGeometry.Etale
