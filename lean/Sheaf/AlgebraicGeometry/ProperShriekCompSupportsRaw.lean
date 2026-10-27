/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S5
-/
module

public import Sheaf.AlgebraicGeometry.ProperSupportedKunnethRoute
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-! Raw proper compositor compatibility after canonicalizing the composite.
Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
(blueprint: lem-sf-proper-shriek-compositor-supports-raw)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/--
The compact-support composition isomorphism for `p` and `f`, followed by the
canonical proper comparison for `p ≫ f`, equals the ordinary composition path.
This is the compositor calculation after the equality-congruence part has been
removed.  It is strictly simpler than the route statement because the target
map is the definitional composite `p ≫ f` and no extra morphism-equality
transport is present.
Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, first supported coordinate extraction before a trace.
-/
theorem properShriekComp_comp_forgetSupports_raw {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S)
    [IsProper p] [IsProper f] (E : DerivedCategoryModule A W) :
    (rightDerivedLowerShriekCompIso A p f).inv.app E ≫
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
