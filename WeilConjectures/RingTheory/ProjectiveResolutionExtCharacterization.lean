/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import WeilConjectures.RingTheory.ProjectiveResolutionExtAllDegrees

/-!
# Bounded projective resolutions and Ext vanishing

A projective resolution of length at most `n` exists if and only if Ext vanishes in degree
`n + 1` against every module, if and only if it vanishes in every degree at least `n + 1`.

## Implementation details

Forward direction by induction on the bound, using the long exact Ext sequence of
`0 → K → P₀ → X → 0`. Conversely, induct on `n`: for `n = 0` the Ext-one criterion makes `X`
projective; at the next bound, take the free module `F` on the underlying set of `X` with
kernel `K`, obtain a length-`n` resolution of `K` by induction and append `F → X`.
The explicit `HasExt.standard` term merely chooses the small model of Ext. The module universe
`max u v` contains the ring, so categorical projectivity agrees with module projectivity and
free resolutions stay in this universe.

## References

* [Stacks, Tag 065R] (1)--(3)
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ModuleCat

/-- A resolution of length at most `n` is equivalent both to vanishing of Ext in degree
`n + 1` against every module and to vanishing in every degree at least `n + 1`.
`n + 1` against every module and to vanishing in every degree at least `n + 1`. -/
theorem hasProjectiveResolutionLE_iff_ext_vanishing
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    (HasProjectiveResolutionLE X n ↔
      ∀ Y : ModuleCat.{max u v} R,
        Subsingleton
          (@Abelian.Ext _ _ _ (HasExt.standard (ModuleCat.{max u v} R)) X Y (n + 1))) ∧
    (HasProjectiveResolutionLE X n ↔
      ∀ (Y : ModuleCat.{max u v} R) (i : ℕ), n + 1 ≤ i →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard (ModuleCat.{max u v} R)) X Y i)) := by
  let := HasExt.standard (ModuleCat.{max u v} R)
  refine ⟨?_, projective_resolution_ext_all_degrees X n⟩
  constructor
  · intro h Y
    let := (hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE X n).mp h
    exact HasProjectiveDimensionLT.subsingleton X (n + 1) (n + 1) le_rfl Y
  · intro h
    exact (hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE X n).mpr
      (hasProjectiveDimensionLT_of_enoughInjectives X (n + 1) h)

end ModuleCat
