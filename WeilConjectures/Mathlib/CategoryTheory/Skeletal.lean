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

## Main definitions

- `CategoryTheory.isoOfToSkeletonEq`: an isomorphism between two objects with the same class in
  the skeleton.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] {X Y : C}

/-- A choice of isomorphism between two objects with the same class in the skeleton. -/
noncomputable def isoOfToSkeletonEq (h : toSkeleton X = toSkeleton Y) : X ≅ Y :=
  (toSkeleton_eq_toSkeleton_iff.1 h).some

end CategoryTheory
