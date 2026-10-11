/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# Finite projective and global dimension

Source: Stacks Project, Algebra, Definitions 00O4 and 00O6
(blueprint: def-weil-pbc-finite-global-dimension).
-/

@[expose] public section

universe u v

namespace ModuleCat

open CategoryTheory

/-- A projective resolution of `M` of length at most `n` is exact, has projective
terms, and has zero terms in degrees greater than `n`. The exactness and
projectivity are fields of `ProjectiveResolution`. Source: Stacks Project,
Algebra, Definition 00O4 (blueprint: def-weil-pbc-finite-global-dimension). -/
def HasProjectiveResolutionLE {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (n : ℕ) : Prop :=
  ∃ P : ProjectiveResolution M, ∀ i : ℕ, n < i → CategoryTheory.Limits.IsZero (P.complex.X i)

/-- A module has finite projective dimension when it has a projective resolution
of some finite length. Source: Stacks Project, Algebra, Definition 00O4
(blueprint: def-weil-pbc-finite-global-dimension). -/
def HasFiniteProjectiveDimension {R : Type u} [CommRing R] (M : ModuleCat.{v} R) :
    Prop :=
  ∃ n : ℕ, HasProjectiveResolutionLE M n

/-- The projective dimension of a module with finite projective dimension is
the least length of a projective resolution. Source: Stacks Project, Algebra,
Definition 00O4 (blueprint: def-weil-pbc-finite-global-dimension). -/
noncomputable def projectiveDimension {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (h : HasFiniteProjectiveDimension M) : ℕ :=
  by classical exact Nat.find h

end ModuleCat

namespace Ring

/-- A ring has global dimension at most `n` when every module has a projective
resolution of length at most `n`, with no finite generation assumption.
Source: Stacks Project, Algebra, Definition 00O6
(blueprint: def-weil-pbc-finite-global-dimension). -/
def HasGlobalDimensionLE (R : Type u) [CommRing R] (n : ℕ) : Prop :=
  ∀ M : ModuleCat.{v} R, ModuleCat.HasProjectiveResolutionLE M n

/-- A ring has finite global dimension if one finite length bounds projective
resolutions of all its modules. Source: Stacks Project, Algebra, Definition 00O6
(blueprint: def-weil-pbc-finite-global-dimension). -/
def HasFiniteGlobalDimension (R : Type u) [CommRing R] : Prop :=
  ∃ n : ℕ, HasGlobalDimensionLE.{u, v} R n

/-- The global dimension of a ring of finite global dimension is the least
uniform bound for projective resolutions of all its modules. Source: Stacks
Project, Algebra, Definition 00O6
(blueprint: def-weil-pbc-finite-global-dimension). -/
noncomputable def globalDimension (R : Type u) [CommRing R]
    (h : HasFiniteGlobalDimension.{u, v} R) : ℕ :=
  by classical exact Nat.find h

end Ring
