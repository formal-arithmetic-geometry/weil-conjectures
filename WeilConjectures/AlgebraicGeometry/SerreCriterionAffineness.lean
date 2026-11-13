/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealH1Representatives
import WeilConjectures.AlgebraicGeometry.QuasiCompactH1Zero

/-!
# Serre's criterion for affineness

## References

* [Stacks Project, Tag 01XG](https://stacks.math.columbia.edu/tag/01XG)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact, quasi-separated scheme is affine if the first cohomology of every
quasi-coherent ideal sheaf of finite type vanishes. Quasi-coherent ideal sheaves are
`X.IdealSheafData`, and `I.toModules` is their associated submodule of `𝒪_X`. -/
theorem isAffine_of_finiteType_ideal_h1_zero (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (h : ∀ I : X.IdealSheafData, I.toModules.IsFiniteType →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules)) :
    IsAffine X := by
  apply AlgebraicGeometry.quasiCompact_affine_of_h1_ideal_zero X
  intro I hI
  have hzero : ∀ x : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules,
      x = 0 := by
    intro x
    obtain ⟨K, _, hK, f, y, _, hy⟩ := ideal_h1_finiteType_representative X I hI x
    have := ModuleCat.subsingleton_of_isZero (h K hK)
    rw [← hy, Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

end AlgebraicGeometry.Scheme
