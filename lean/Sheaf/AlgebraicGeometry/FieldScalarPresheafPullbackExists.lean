/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.FieldScalarPresheafRingMap
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

/-! # Existence of presheaf scalar extension in larger universes

Source: Stacks Project, Sheaves on Spaces, Tag 0096; Mathlib's presheaf pullback construction.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafOfModules

/-- Restriction from R-module presheaves to constant-ring module presheaves has a
left adjoint, also when the modules live in a universe larger than the site.

Source: Stacks Project, Sheaves on Spaces, Tag 0096; Mathlib presheaf pullback construction.
(blueprint: lem-sc-field-scalar-presheaf-pullback-exists).

Proof: for each open U, form R(U) tensor over k with the sections of the input
presheaf. For a possibly noncommutative R(U), the right k-action is
r · c = r α_U(c), and the left R(U)-action is left multiplication. The restriction
maps send r tensor m to r restricted tensor m restricted. The balanced relations
are respected because α is natural. A map out of this presheaf is determined by
its values on 1 tensor m. Conversely a natural k-linear map to scalar restriction
extends uniquely by r tensor m mapping to r times the image of m. These are
inverse natural hom bijections and give the adjunction. Tensor products and
sectionwise quotients stay in Type (max u v), since the rings and the site are
u-small. This proves the existence without a field hypothesis, and includes the
zero ring and empty space. The adjunction determines the extension functor up
to unique natural isomorphism; no arbitrary algebraic object is chosen. -/
theorem fieldScalarPresheafPullback_isRightAdjoint
    {k : Type u} [Ring k] (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (α : k →+* R.obj.obj (op ⊤)) :
    (PresheafOfModules.pushforward.{max u v}
      (fieldScalarPresheafRingMap X R α)).IsRightAdjoint := by sorry

end SheafOfModules
