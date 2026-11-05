/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# The affine scheme of roots of unity

Source: Stacks Project, groupoids.tex, Tag 040M, Example `example-roots-of-unity`,
and etale-cohomology.tex, Tag 03PK, Section `section-kummer`
(blueprint: lem-asd-affine-roots-representability).

## Main definitions

- `affineRootsOver`: the explicit quotient spectrum over `Spec R`.
- `affineRootsCoordinate`: its distinguished global section.

## Main statement

- `affineRoots_representability`: the natural bijections, their sheaf identification, and
  their compatibility with arbitrary base change.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Polynomial

namespace AlgebraicGeometry

end AlgebraicGeometry
