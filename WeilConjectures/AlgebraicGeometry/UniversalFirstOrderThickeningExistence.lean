/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningAffineLocal
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningAffineGlobalization

/-!
# Existence part of universal first order thickenings

A formally unramified morphism of schemes admits a universal first order thickening.

## References

* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A formally unramified morphism admits a universal first order thickening. -/
theorem FormallyUnramified.exists_universalFirstOrderThickening_existence
    {Z X : Scheme.{u}} (h : Z ⟶ X) [FormallyUnramified h] :
    ∃ (Z' : Scheme.{u}) (i : Z ⟶ Z') (h' : Z' ⟶ X),
      IsUniversalFirstOrderThickening h i h' := by
  obtain ⟨Z', i, h', hi, hcomp, haffine⟩ :=
    FormallyUnramified.exists_affine_local_universalFirstOrderThickening h
  exact ⟨Z', i, h', isUniversalFirstOrderThickening_of_affine_local
    h i h' hi hcomp haffine⟩

end AlgebraicGeometry
