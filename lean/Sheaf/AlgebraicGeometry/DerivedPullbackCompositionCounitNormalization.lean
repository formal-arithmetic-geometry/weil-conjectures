/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCompositionCounitApex
public import Sheaf.AlgebraicGeometry.SchemeDerivedMateEvaluation

/-! # Counit calculations for pullback composition
Source: Stacks Project, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-pullback-composition-counit-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry
variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

set_option maxHeartbeats 800000 in
-- The selected adjunctions and composite sheaf instances need a larger budget.
/-- The chosen pullback comparison and composite direct-image unit transpose to the
explicit pasted underived counits.
Source: Stacks Project, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-pullback-composition-counit-normalization).

Proof: Apply the pinned Hom formula at the underived counit for f ≫ g; its
adjunct is the identity by the right triangle identity. Thus L(fg) applied to β(fg),
followed by the derived counit, is ε(fg) at (fg)_*K followed by the localized
underived counit. Precompose with p. The defining left-derived lift factorization
replaces p followed by ε(fg) by Lf(ε(g)), ε(f), and the localized tensor
composition comparison. On a complex representative, the comparison is the inverse
mate of pushforwardComp, so its composite with the (fg)-counit is the pasted
g- and f-counits: apply conjugateEquiv_counit_symm degreewise, and use that
pushforwardComp is the identity on sections. Descend through the homotopy quotient
and apply localization. Naturality of ε(f) at the g-counit moves the localized
g-counit inside Lf and gives the displayed formula. Identities, zero complexes and
empty schemes use the same triangle and naturality equations. -/
theorem derivedPullbackComposition_counit_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (canonicalDerivedPullbackComposition f g).hom.app
        (((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) ≫
      (derivedPullback (f ≫ g)).map
        ((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K) ≫
      (schemeHomPullbackAdjunction (f ≫ g)).counit.app (DerivedCategory.Qh.obj K) =
      derivedCompositionCounitApex f g K
    := by sorry

end AlgebraicGeometry
