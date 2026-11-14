/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSurjectivePullback

/-!
# Descent of constructibility along a surjective morphism

Source: Stacks Project, Etale Cohomology, Tag 095Q (3), converse for finite coefficient
rings.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Constructibility of a sheaf of modules over a finite commutative ring descends along
any surjective morphism between quasi-compact quasi-separated schemes. Constructibility
on both sides means the same finite constructible, locally closed stratification with
finite locally constant module values.

Source: Stacks Project, Etale Cohomology, Tag 095Q (3), converse for finite coefficient
rings. -/
theorem isConstructibleEtaleModuleSheaf_of_surjective_pullback
    {T U : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace U] [QuasiSeparatedSpace U] (a : T ⟶ U) [Surjective a]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleEtaleModuleSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).obj G)) :
    IsConstructibleEtaleModuleSheaf G := by
  exact (isConstructibleEtaleModuleSheaf_iff_surjective_pullback a G).mpr hG

end AlgebraicGeometry.Scheme
