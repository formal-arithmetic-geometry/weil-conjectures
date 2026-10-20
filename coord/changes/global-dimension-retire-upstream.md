# GlobalDimension duplicate retirement

## Reason

The retire-first queue assigns this zero-hole definition module because its duplicate
names collide with the adopted upstream GlobalDimension. Three rework roots report
`environment already contains 'Ring.HasFiniteGlobalDimension'`. Use the adopted
source without changing it. The definitions of the bounded-resolution predicate are
verbatim identical. Upstream finite projective dimension and global dimension bounds
use Ext vanishing instead of bounded resolutions. The already proved equivalence in
WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension (Stacks 065R)
identifies them at ModuleCat.{max u v}, the universe used by the remaining consumer.

## Old

The withdrawn module, verbatim:

```lean
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
```

## New

Withdraw lean/Sheaf/RingTheory/GlobalDimension.lean through deleted.txt; the landing
leaves an empty module. Use the following existing upstream module, unchanged:

```lean
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
(`ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE`, Stacks Lemma 065R).

Source: Stacks Project, Algebra, Definitions 00O4 and 00O6
(blueprint: def-weil-pbc-finite-global-dimension).
-/

@[expose] public section

universe u v

namespace ModuleCat

open CategoryTheory

/-- A projective resolution of `M` of length at most `n`: a projective resolution whose terms
vanish in degrees greater than `n`. This is equivalent to Mathlib's
`CategoryTheory.HasProjectiveDimensionLE M n`
(`ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE`). Source: Stacks Project,
Algebra, Definition 00O4 and Lemma 065R. -/
def HasProjectiveResolutionLE {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (n : ℕ) : Prop :=
  ∃ P : ProjectiveResolution M, ∀ i : ℕ, n < i → CategoryTheory.Limits.IsZero (P.complex.X i)

/-- A module has finite projective dimension when it has projective dimension at most `n`, in
the sense of Mathlib's `CategoryTheory.HasProjectiveDimensionLE`, for some `n`. Its projective
dimension is Mathlib's `CategoryTheory.projectiveDimension M`. Source: Stacks Project, Algebra,
Definition 00O4 (blueprint: def-weil-pbc-finite-global-dimension). -/
def HasFiniteProjectiveDimension {R : Type u} [CommRing R] (M : ModuleCat.{v} R) :
    Prop :=
  ∃ n : ℕ, HasProjectiveDimensionLE M n

end ModuleCat

namespace Ring

/-- A ring has global dimension at most `n` when every module has projective dimension at most
`n` (Mathlib's `CategoryTheory.HasProjectiveDimensionLE`), with no finite generation assumption.
Source: Stacks Project, Algebra, Definition 00O6
(blueprint: def-weil-pbc-finite-global-dimension). -/
def HasGlobalDimensionLE (R : Type u) [CommRing R] (n : ℕ) : Prop :=
  ∀ M : ModuleCat.{v} R, CategoryTheory.HasProjectiveDimensionLE M n

/-- A ring has finite global dimension if one finite bound holds for the projective dimensions
of all its modules. Source: Stacks Project, Algebra, Definition 00O6
(blueprint: def-weil-pbc-finite-global-dimension). -/
def HasFiniteGlobalDimension (R : Type u) [CommRing R] : Prop :=
  ∃ n : ℕ, HasGlobalDimensionLE.{u, v} R n

/-- The global dimension of a ring of finite global dimension is the least
uniform bound for the projective dimensions of all its modules. Source: Stacks
Project, Algebra, Definition 00O6
(blueprint: def-weil-pbc-finite-global-dimension). -/
noncomputable def globalDimension (R : Type u) [CommRing R]
    (h : HasFiniteGlobalDimension.{u, v} R) : ℕ :=
  by classical exact Nat.find h

end Ring
```

ModuleCat.projectiveDimension, the unused natural-number minimum, has no callers and
is withdrawn. It is not replaced by CategoryTheory.projectiveDimension: that function
has a different type and returns bottom at the zero module. The node attachment no
longer claims to realize that clause. The projective-resolution predicate and global
minimum retain their meanings, including the zero module, zero ring and bound zero.

## Users

`tools/downstream.py Sheaf.RingTheory.GlobalDimension --direct --uses ...` reports
exactly one importer; the transitive count is also one. A whole-library rg confirms
there are no uses of ModuleCat.projectiveDimension outside the withdrawn module.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.GlobalDimension | A3 | Retire duplicate definitions; reattach node upstream. |
| Sheaf.Algebra.ProjectiveDimensionWellDefined | unclaimed | Redirect public import upstream; add private bounded-resolution bridge import; convert the last uniform bound through the bridge before and after padding. Its theorem signature and visibility stay verbatim. |

The original consumer with only its import redirected fails at its final `pad` call:
`Nat.find_spec hex N` has type `HasProjectiveDimensionLE N (Nat.find hex)` but
`N.HasProjectiveResolutionLE (Nat.find hex)` is expected. The three added proof lines
perform exactly those conversions. All other proof lines and the docstring stay.
The adapted module compiles through lcompile.py in 1.7 seconds with no warnings.

No Challenge statement or definition in its elaborated type is changed. The changed
interpretation of uniform bounds is justified by the existing exact equivalence;
the independent review should recheck the global-dimension definition attachment.
No upstream file, signature, attribute, public import or body is changed.

## Status

landed 20261020T144233-L-2257551 2026-10-20 (merge of deliver/A3/Sheaf.RingTheory.GlobalDimension)
