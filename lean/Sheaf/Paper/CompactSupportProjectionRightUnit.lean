/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.Paper.AffineLinePurityCoordinateMaps

/-! # Right-unit normalization of the compactification projection

The coefficient unit is the literal comparison image of the ordinary constant complex.
Source: Stacks, Tags 0B56, 07A4 and 0GL1
(blueprint: lem-pur-compact-support-projection-right-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.AffineLinePurity
open VectorIntegrationSite

/-- The actual proper-counit/open-tensor projection is right unital, with the literal
compared coefficient unit. No invertibility of its unit component is required.
Source: Stacks, Cohomology on Sites, Tags 0B56 and 07A4 at the tensor unit, and
Tag 0GL1, lemma-j-shriek-and-tensor
(blueprint: lem-pur-compact-support-projection-right-unit).
Proof: write the compactification as f = pj and its direct image as F = Rp_* j_!.
Expand the published projection into the proper counit mate followed by Rp_* of the
inverse open tensor comparison and the pullback compositor. The proper mate at the
coefficient unit, followed by Rp_* of the pullback-unit map and right unitor, is the
right unitor by its adjunction triangle and tensor-unit compatibility. For the open
factor, restrict the tensor comparison to j. Its prescribed normalization is the
identity, and j_! is fully faithful, so faithfulness identifies its unit specialization
with j_! of the right unitor and the pullback-unit identification. Pullback-unit
composition identifies the consecutive unit maps for p and j with that for f.
Apply Rp_* to the open equality and substitute the proper mate unit equality.
Finally transport the unit along the canonical comparison image of the ordinary
constant complex; the definitions of pullbackUnit and moduleRightUnit insert precisely
these canonical identifications. This proves the displayed equation for every M,
including zero objects and empty schemes, on the ambient unbounded categories. -/
theorem compactSupportProjection_rightUnit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app (unit A Y) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map (pullbackUnit A f).hom ≫
          (moduleRightUnit A X M).hom) =
      (moduleRightUnit A Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).hom := by
  sorry

end AlgebraicGeometry.ProEtale.AffineLinePurity
