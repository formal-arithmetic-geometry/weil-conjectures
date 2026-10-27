/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.ProperSupportedKunnethRoute
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
import Sheaf.AlgebraicGeometry.ProperShriekCompSupportsRaw

/-! # Canonical-composite proper forget-supports calculation

Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/--
The specified proper compact-support compositor agrees with the raw compositor
when the composite morphism is written canonically. This is the canonical-composite
special case used to transport the raw forget-supports calculation to an arbitrary
specified composite.
Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
(blueprint: lem-sf-proper-shriek-compositor-supports-canonical)
-/
theorem properShriekComp_comp_forgetSupports_canonical {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) [IsProper p] [IsProper f] [IsProper (p ≫ f)]
    (E : DerivedCategoryModule A W) :
    (properRouteCompIso A p f (p ≫ f) rfl).inv.app E ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (p ≫ f)).hom.app E =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) p).hom.app E) ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) f).hom.app
            ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj E) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) p f (p ≫ f) rfl).hom.app E := by
  sorry

end AlgebraicGeometry.Etale
