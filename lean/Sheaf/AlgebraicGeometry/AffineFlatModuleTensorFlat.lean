/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Tensor flatness from flat sections on all affine subopens

Source: Stacks Project, Tags 05NE, 00H9 and 00HT.
(blueprint: lem-pc-affine-flat-module-tensor-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Affine-local flatness over the identity implies tensor-exact sheaf flatness.
Source: Stacks Project, Modules, Tag 05NE; flatness and filtered colimits, Tag 00H9.
(blueprint: lem-pc-affine-flat-module-tensor-flat).

Proof: Fix a point x and an affine neighbourhood V. For every affine neighbourhood
U of x contained in V, the hypothesis makes G(U) flat over O(V), with scalars
restricted along O(V) -> O(U). These U form a filtered neighbourhood basis.
Their filtered colimit is G_x as an O(V)-module, so it is flat over O(V).
The stalk ring O_x is the localization of O(V) at the prime of x. Since G_x is
already an O_x-module, localization of G_x over O(V) is canonically G_x itself.
Base change of a flat module is flat; thus G_x is flat over O_x. Tensor products
of module sheaves have the corresponding tensor products as stalks. Tensoring
any short exact sequence with G is therefore exact on every stalk, and hence
exact as a sequence of sheaves. Tensoring also preserves finite colimits by its
right exactness, giving the stated exact functor. No quasi-coherence is used:
the hypothesis controls all affine subopens, not just the sections over V.
The empty scheme has no stalks and its module category is trivial; the zero
sheaf satisfies the same argument. -/
theorem isFlat_of_affineFlatOver_identity {Y : Scheme.{u}} (G : Y.Modules)
    (hflat : Scheme.Modules.IsFlatOver G (𝟙 Y)) : SheafOfModules.IsFlat G := by
  sorry

end AlgebraicGeometry
