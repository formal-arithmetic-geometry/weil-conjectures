/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Skeletal

/-!
# Objects with the same class in the skeleton are isomorphic

`CategoryTheory.toSkeleton_eq_toSkeleton_iff` says that two objects of a category have the same
class in its skeleton if and only if they are isomorphic, but it only produces a `Nonempty`.
This file chooses an isomorphism.

The choice is made with `Nonempty.some`, so the resulting isomorphism is *arbitrary*: it is not
natural in either object, it satisfies no compatibility with composition or with any monoidal
structure, and two applications of `CategoryTheory.isoOfToSkeletonEq` to equal data are equal
only because of proof irrelevance of the hypothesis. Nothing beyond the existence of an
isomorphism can be proved about it, so a construction that has a canonical isomorphism available
should use that one instead.

## Main definitions

- `CategoryTheory.isoOfToSkeletonEq`: an isomorphism between two objects with the same class in
  the skeleton.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] {X Y : C}

/-- A choice of isomorphism between two objects with the same class in the skeleton.

This isomorphism is an arbitrary one: it is produced by `Nonempty.some` and satisfies no
naturality or coherence property whatsoever. -/
noncomputable def isoOfToSkeletonEq (h : toSkeleton X = toSkeleton Y) : X ≅ Y :=
  (toSkeleton_eq_toSkeleton_iff.1 h).some

end CategoryTheory
