/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
import WeilConjectures.AlgebraicGeometry.ProperShriekCompSupportsCanonical

/-! # Proper forget supports and the specified compact-support compositor
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The specified compact-support compositor transports to the ordinary compositor.
(Stacks, Tags 07A7, 0D6E) -/
theorem properShriekComp_comp_forgetSupports {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) (h : W ⟶ S) (w : p ≫ f = h)
    [IsProper p] [IsProper f] [IsProper h] (E : DerivedCategoryModule A W) :
    (properRouteCompIso A p f h w).inv.app E ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) h).hom.app E =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) p).hom.app E) ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) f).hom.app
            ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj E) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) p f h w).hom.app E := by
  subst h
  exact properShriekComp_comp_forgetSupports_canonical A p f E

end AlgebraicGeometry.Etale
