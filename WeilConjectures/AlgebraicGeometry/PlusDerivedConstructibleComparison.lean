/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteOpenCoverDirectImageSpectralSequence

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Etale

/-- Comparison of ordinary right-derived lower-star cohomology with the plus-derived model. -/
theorem constructible_plus_homology_of_rightDerived
    {k : Type (u + 1)} [CommRing k] [Finite k]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k))
    (q : ℤ) (hq : 0 ≤ q)
    (h : Scheme.IsConstructibleSheaf (((lowerStar (ModuleCat.{u + 1} k) f).rightDerived q.toNat).obj M)) :
    Scheme.IsConstructibleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} k)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} k) f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) := by
  sorry

end AlgebraicGeometry.Etale
