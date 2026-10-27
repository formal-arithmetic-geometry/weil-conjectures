module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Composition of proper morphisms of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 04XY (lemma-composition-proper)
(blueprint: lem-sfb-space-proper-composition).

Properness is the existing algebraic-space predicate: separated, of finite type, and
universally closed. No representability or local Noetherian hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A composite of proper morphisms of algebraic spaces over Spec ℤ is proper.
Source: Stacks Project, Morphisms of Spaces, Tag 04XY (lemma-composition-proper)
(blueprint: lem-sfb-space-proper-composition).

Proof:
1. The separated-composition clause of lem-sfb-space-separated-fp-composition shows
   that the composite is separated. This uses neither finite presentation nor
   representability of the two maps.
2. The algebraic-space clause of lem-sfb-stack-finite-type-calculus gives local finite
   type of the composite. For a quasi-compact open W in Z, its inverse image in Y is
   a quasi-compact open, and its further inverse image in X is quasi-compact. Thus
   the composite is quasi-compact and of finite type.
3. For every algebraic-space base change T → Z, the sheaf fibre products are algebraic
   spaces by lem-trf-space-fibre-products-etale-covers. The universal property identifies
   X ×_Y (Y ×_Z T) with X ×_Z T. The two resulting projections to Y ×_Z T and T are
   closed on point spaces by universal closedness of the two original maps. Images
   of closed sets remain closed under their composite, so the composite is universally
   closed. Maps on field-valued point classes compose, giving the asserted point map.
4. Separatedness, finite type and universal closedness are precisely properness. -/
theorem mapIsProper_comp
    {X Y Z : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : MapIsProper f) (hg : MapIsProper g) :
    MapIsProper (f ≫ g) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
