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

/-!
# Bounded projective resolutions and Ext vanishing in all degrees

A module has a projective resolution of length at most `n` if and only if Ext against every
module vanishes in every degree at least `n + 1`.

## Implementation details

Induct on the resolution bound. A bounded projective resolution gives a long exact Ext sequence
whose projective term contributes no positive Ext. Conversely, the kernel of a free epimorphism
onto `X` inherits the shifted vanishing, and splicing its shorter resolution with that
epimorphism gives a resolution of `X`. The argument is performed in `ModuleCat`;
`HasExt.standard` merely chooses the standard small Ext model.

## References

* [Stacks, Tag 065R]
-/

@[expose] public section
universe u v
open CategoryTheory
namespace ModuleCat
/-- One component of Stacks 065R: a projective resolution of length at most `n` exists if and
only if Ext vanishes in every degree at least `n + 1`. -/
theorem projective_resolution_ext_all_degrees
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    (HasProjectiveResolutionLE X n ↔
      ∀ (Y : ModuleCat.{max u v} R) (i : ℕ), n + 1 ≤ i →
        Subsingleton
          (@Abelian.Ext _ _ _ (HasExt.standard (ModuleCat.{max u v} R)) X Y i)) := by
  let := HasExt.standard (ModuleCat.{max u v} R)
  constructor
  · intro h Y i hi
    let := (hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE X n).mp h
    exact HasProjectiveDimensionLT.subsingleton X (n + 1) i hi Y
  · intro h
    apply (hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE X n).mpr
    apply HasProjectiveDimensionLT.mk
    intro i hi Y e
    exact (h Y i hi).elim _ _
end ModuleCat
