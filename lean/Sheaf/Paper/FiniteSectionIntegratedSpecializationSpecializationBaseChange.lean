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

/-- The normalized zero-fibre specialization square for the normal exchange.
Source: finite-ring section deformation base-change compatibility.
(blueprint: lem-sp-finite-section-integrated-specialization-base-change).
This is strictly the specialization factor of the integrated square. -/
theorem specialization_normalExchange
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
    (ν : s'.ker.normalCone ⟶ s.ker.normalCone)
    (sqν : IsPullback ν (Scheme.Hom.normalConeProj g' s')
      (Scheme.Hom.normalConeProj g s) b)
    (hzero : s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection)
    (κ : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s))
    (κ' : NoetherianSectionSpecialization.family A g' s' ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).obj
        (sectionInvariant A g' s'))
    (hκ : NoetherianSectionSpecialization.Normalized A g s hs κ)
    (hκ' : NoetherianSectionSpecialization.Normalized A g' s' hs' κ') :
    (ordinaryFinitePullback A b).map
        (NoetherianSectionSpecialization.specialization A g s κ) ≫
      NoetherianSectionSpecialization.sectionMap A
        (Scheme.Hom.normalConeProj g s) (Scheme.Hom.normalConeProj g' s') b ν sqν
        s.normalConeZeroSection s'.normalConeZeroSection hzero =
      NoetherianSectionSpecialization.sectionMap A g g' b q cart s s' hsec ≫
        NoetherianSectionSpecialization.specialization A g' s' κ' := by
  sorry


end AlgebraicGeometry.Etale.FiniteSmoothPurity
