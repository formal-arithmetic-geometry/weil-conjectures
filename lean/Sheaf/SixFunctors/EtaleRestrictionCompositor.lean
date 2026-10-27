/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y8
-/
module

public import Sheaf.Paper.EtaleCompactSupportCoefficientChange

/-! # Scalar restriction and the canonical etale compositor

Source: Stacks Project, more-etale.tex, Tags 0F7J and 0GL6.
(blueprint: lem-sf-etale-restriction-compositor).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- Scalar restriction commutes with the specified compact-support compositor.
Source: Stacks Project, Tags 0F7J and 0GL6
(blueprint: lem-sf-etale-restriction-compositor).

Proof: compute the compositor on the compatible compactification triangle. On its
proper factors, restriction commutes with the direct-image compositors by the
K-injective normalization of the derived direct-image comparison. On the open
factors, transpose under the extension-by-zero adjunction: both paths are the same
restriction/inverse-image identification, so the unit identities give equality.
For the mixed factor, paste that identification with the cartesian inverse-image
square and take mates. This proves the restriction square for proper/open
interchange. Whisker these three equations to obtain the square for the triangle.
For an arbitrary chosen compactification, express its refinement comparison as
proper pushforward of the proper/open comparison. The same mate calculation
commutes restriction with each refinement; adjacent inverse refinement maps
cancel. This is the displayed equation for the canonical chosen compositor.
No scalar tensor, finite Tor amplitude or faithfulness of derived restriction is
used. Identity ring maps and identity geometric maps give the respective unit
identities; the zero coefficient ring is included. -/
theorem compactSupportRestrictionPlus_compositor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (rightDerivedLowerShriekPlusCompIso A f g).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (compactSupportCoefficientRestrictionPlus φ
        (HasCompactification.compactification (f ≫ g))).hom.app L =
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) g).map
        ((compactSupportCoefficientRestrictionPlus φ
          (HasCompactification.compactification f)).hom.app L) ≫
      (compactSupportCoefficientRestrictionPlus φ
        (HasCompactification.compactification g)).hom.app
          ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} B) f).obj L) ≫
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        ((rightDerivedLowerShriekPlusCompIso B f g).hom.app L) := by sorry

end AlgebraicGeometry.Etale
