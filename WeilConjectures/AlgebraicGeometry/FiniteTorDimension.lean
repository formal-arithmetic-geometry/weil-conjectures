/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes

/-! # Finite Tor dimension on a scheme

## References

* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A derived object has finite Tor dimension when one finite interval bounds the
cohomology of its derived tensor with every module sheaf. The interval is global,
independent of the test module. (Stacks, Tag 08CG.) -/
def HasFiniteTorDimension (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧
    ∀ F : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X E F i

end AlgebraicGeometry.Scheme
