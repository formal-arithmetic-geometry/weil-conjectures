/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.RingHom.Flat

/-! # Stalkwise flatness over the direct-image algebra
Source: Stacks Project, Tag 0AVW.
(blueprint: lem-sc-affine-algebra-stalk-flat)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The canonical morphism to the direct-image algebra is stalkwise flat.
Source: Stacks Project, Tag 0AVW, affine stalk calculation in the proof.
(blueprint: lem-sc-affine-algebra-stalk-flat)

Proof: choose an affine neighborhood Spec B of f(x). Its inverse image is Spec A
because f is affine. Write p for x and q for its image. Distinguished neighborhoods
D(b), b outside q, are cofinal among neighborhoods of q. Their inverse images have
sections A localized at the image of b. Taking the colimit identifies the source
stalk with S⁻¹A, where S is the image of B minus q. The target stalk is A_p, and
naturality of germs identifies the canonical stalk map with the localization map
S⁻¹A → A_p. Since S avoids p, this is a further localization and therefore flat.
The calculation is local around every x; for empty X the assertion is vacuous. -/
theorem affine_algebra_stalkMap_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (x : X) :
    ((toDirectImageAlgebraSpace f).hom.stalkMap x).hom.Flat := by sorry

end AlgebraicGeometry
