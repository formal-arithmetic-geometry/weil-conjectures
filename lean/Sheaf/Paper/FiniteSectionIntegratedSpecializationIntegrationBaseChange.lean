/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteSmoothPurityMaps
public import Sheaf.Paper.VectorPurityNormalization
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The inverse-normal-bundle integration square for the normal exchange.
Source: Kummer-normalized vector integration trace base-change.
(blueprint: lem-sp-finite-section-integrated-specialization-base-change).
This is the integration factor of the integrated square, strictly below the target. -/
theorem normalExchange_integration
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S V' S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S']
    (d : ℕ) (g : V ⟶ S) (g' : V' ⟶ S')
    [SmoothOfRelativeDimension d g] [SmoothOfRelativeDimension d g']
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    [IsSeparated g'] [QuasiCompact g'] [HasCompactification g']
    (s : S ⟶ V) (s' : S' ⟶ V') [IsClosedImmersion s] [IsClosedImmersion s']
    [FiniteRingSectionDeformation.Geometry d g s]
    [FiniteRingSectionDeformation.Geometry d g' s']
    (hs : s ≫ g = 𝟙 S) (hs' : s' ≫ g' = 𝟙 S')
    (b : S' ⟶ S) (q : V' ⟶ V) (cart : IsPullback q g' g b)
    (hsec : s' ≫ q = b ≫ s)
    (sq : IsPullback
      ((reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s).hom)
      (Scheme.Hom.normalConeProj g s)
      (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)) (𝟙 S))
    (sq' : IsPullback
      ((reesConeComparison s' ≪≫ FiniteRingSectionDeformation.coneBundleIso d g' s').hom)
      (Scheme.Hom.normalConeProj g' s')
      (VectorBundleZeroSection.π S' d (ConormalGradedAlgebra.piece s' 1)) (𝟙 S'))
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤)))
    (ν : s'.ker.normalCone ⟶ s.ker.normalCone)
    (sqν : IsPullback ν (Scheme.Hom.normalConeProj g' s')
      (Scheme.Hom.normalConeProj g s) b)
    (hzero : s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection)
    (hn : IsIso (normalSectionMap A d g s hs sq))
    (hn' : IsIso (normalSectionMap A d g' s' hs' sq')) :
    (ordinaryFinitePullback A b).map
        ((@inv _ _ _ _ (normalSectionMap A d g s hs sq) hn) ≫
          (FiniteRingSectionDeformation.bundleOrientation N hN A hA S hS d
            (ConormalGradedAlgebra.piece s 1)).hom) ≫
        (vectorIntegrationBaseCoefficientPullback A N hA
          (WeilConjectures.PurityFiniteSetting.purityTwistTransport A N hN hA) b hS d).hom =
      NoetherianSectionSpecialization.sectionMap A
        (Scheme.Hom.normalConeProj g s) (Scheme.Hom.normalConeProj g' s') b ν sqν
        s.normalConeZeroSection s'.normalConeZeroSection hzero ≫
        (@inv _ _ _ _ (normalSectionMap A d g' s' hs' sq') hn') ≫
        (FiniteRingSectionDeformation.bundleOrientation N hN A hA S' hS' d
          (ConormalGradedAlgebra.piece s' 1)).hom := by
  sorry


end AlgebraicGeometry.Etale.FiniteSmoothPurity
