/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Finite projective and global dimension

Projective dimension is Mathlib's `CategoryTheory.HasProjectiveDimensionLE` and
`CategoryTheory.projectiveDimension`, defined by the vanishing of `Ext`. In terms of it we
define modules of finite projective dimension and the global dimension of a ring.

The predicate `ModuleCat.HasProjectiveResolutionLE M n` asks for an explicit projective
resolution of length at most `n`; it is used to construct resolutions, and it is equivalent to
`HasProjectiveDimensionLE M n`
(`ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE`).

## References

* [Stacks, Tag 00O4]
* [Stacks, Tag 00O6]
* [Stacks, Tag 065R]
-/

@[expose] public section

universe u v

namespace ModuleCat

open CategoryTheory

/-- A projective resolution of `M` of length at most `n`: a projective resolution whose terms
vanish in degrees greater than `n`. This is equivalent to Mathlib's
`CategoryTheory.HasProjectiveDimensionLE M n`
(`ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE`). -/
def HasProjectiveResolutionLE {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (n : ℕ) : Prop :=
  ∃ P : ProjectiveResolution M, ∀ i : ℕ, n < i → CategoryTheory.Limits.IsZero (P.complex.X i)

/-- A module has finite projective dimension when it has projective dimension at most `n`, in
the sense of Mathlib's `CategoryTheory.HasProjectiveDimensionLE`, for some `n`. Its projective
dimension is Mathlib's `CategoryTheory.projectiveDimension M`. -/
def HasFiniteProjectiveDimension {R : Type u} [CommRing R] (M : ModuleCat.{v} R) :
    Prop :=
  ∃ n : ℕ, HasProjectiveDimensionLE M n

end ModuleCat

namespace Ring

/-- A ring has global dimension at most `n` when every module has projective dimension at most
`n` (Mathlib's `CategoryTheory.HasProjectiveDimensionLE`), with no finite generation assumption. -/
def HasGlobalDimensionLE (R : Type u) [CommRing R] (n : ℕ) : Prop :=
  ∀ M : ModuleCat.{v} R, CategoryTheory.HasProjectiveDimensionLE M n

/-- A ring has finite global dimension if one finite bound holds for the projective dimensions
of all its modules. -/
def HasFiniteGlobalDimension (R : Type u) [CommRing R] : Prop :=
  ∃ n : ℕ, HasGlobalDimensionLE.{u, v} R n

/-- The global dimension of a ring of finite global dimension is the least
uniform bound for the projective dimensions of all its modules. -/
noncomputable def globalDimension (R : Type u) [CommRing R]
    (h : HasFiniteGlobalDimension.{u, v} R) : ℕ :=
  by classical exact Nat.find h

end Ring
