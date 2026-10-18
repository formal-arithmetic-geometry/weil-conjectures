/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Open subfunctors of algebraic spaces

Source: Stacks Project, Spaces, Definition of immersions, Tag 02YU;
Properties of Spaces, Tag 03BZ (blueprint: def-a1-space-open-subspace).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Open subspaces are subfunctors whose inclusions are representable by open immersions.
Their order is inclusion of subfunctors, inherited by the subtype.
Source: Stacks, Properties of Spaces, Tag 03BZ (blueprint: def-a1-space-open-subspace). -/
def OpenSubspace {S : Scheme.{u}} (F : AlgebraicSpace S) :=
  {A : Subfunctor F.obj.obj //
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) A.ι}

deriving instance PartialOrder for OpenSubspace

end AlgebraicGeometry.AlgebraicSpace
