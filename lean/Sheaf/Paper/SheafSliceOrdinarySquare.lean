/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Paper.SheafSliceOrdinaryData

/-! # The ordinary ringed square for localization at a sheaf

Source: Stacks Project, Modules on Sites, Tag 04IF, and Sites, Tag 04H1.
(blueprint: lem-sbc-ringed-sheaf-slice-ordinary-square).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedCoefficientCounit

namespace CategoryTheory

/-- Localization at a sheaf commutes with ordinary ringed inverse and direct images.
There are no derived-category or resolution hypotheses.

Source: Stacks Project, Modules on Sites, Tag 04IF; Sites, Tag 04H1;
the ordinary module adjunction, Tag 03D7.
(blueprint: lem-sbc-ringed-sheaf-slice-ordinary-square).

Proof. Present both slices by their element sites. The arrowwise inverse image on
slice categories has right adjoint given by the pullback of the direct image along
the unit at the slicing sheaf. Transfer this adjunction along the fibre equivalences.
The product comparison identifies localization of inverse image with inverse image
of localization; on a fibre this identification is the second projection. Restrict
its structural ring map using this identification. The graph identities for ring
operations transfer to the slice, and give the induced module direct image. Choose
ordinary pullbacks by scalar extension of the algebraic inverse image. Restriction
commutes with this tensor construction and its scalar insertions, producing sigma.
On underlying sheaves the right adjoint sends a product over the pulled-back slicing
sheaf to the corresponding product over the original sheaf. Its fibrewise module
operations are exactly the original induced operations, giving delta with the stated
underlying geometric mate. The scalar-insertion formula for the two adjunctions
shows that sigma and delta are mates. These constructions also apply when the
slicing sheaf is initial or terminal: fibres may be empty, and all identities are
identities on the existing sections, without a choice of a section of that sheaf. -/
theorem ringedSheafSliceOrdinarySquare
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    (A : Sheaf K (Type u)) :
    Nonempty (RingedSheafSliceSquare RX RY f A) := by
  sorry

end CategoryTheory
