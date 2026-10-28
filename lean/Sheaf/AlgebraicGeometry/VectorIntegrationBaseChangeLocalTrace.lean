/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.VectorTraceGeometry

/-! # Geometric local trace exchange before arbitrary-arrow substitution -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/--
The geometric local trace exchange used by the degree-zero base-change wrapper.

Proof: paste the Cartesian exchange square for the source bundle with the coefficient
comparison `c`, then restrict both frame charts to `W`.  The affine counit base-change
identity over `W` identifies the two resulting prefixes.  Substitution of the two
frame equations and naturality of the constant-unit pullback gives the displayed
formula.  This is the geometric core; the wrapper separately handles arbitrary
arrows `kS` and `kT` by pullback composition.
(blueprint: lem-pur-vector-integration-base-local-trace). -/
theorem vectorIntegration_baseChange_local_trace
    (N : ℕ) (hN : 0 < N)
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
    (ha : a ≫ U.ι = j) (hg : j ≫ f = g ≫ V.ι) :
    (ordinaryFinitePullback A j).map b.hom ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a U.ι j ha.symm).hom.app _ ≫
        (ordinaryFinitePullback A a).map
          (vectorIntegrationLocalTrace N hN A hA t D T
            (affineTracePullbackInvertible N f hS) r
            ((Scheme.Modules.tensorPullback f).obj F) U eT) ≫
        (ordinaryFiniteUnitPullback A a).hom =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j f (g ≫ V.ι) hg.symm).inv.app _ ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g V.ι (g ≫ V.ι) rfl).hom.app _ ≫
        (ordinaryFinitePullback A g).map
        (vectorIntegrationLocalTrace N hN A hA t D S hS r F V eS) ≫
        (ordinaryFiniteUnitPullback A g).hom := by
  sorry

end AlgebraicGeometry.Etale
