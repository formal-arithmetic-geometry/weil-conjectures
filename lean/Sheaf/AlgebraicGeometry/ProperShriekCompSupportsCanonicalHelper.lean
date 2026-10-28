/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProperSupportedKunnethRoute
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-! Canonical component normalization for the proper compact-support compositor. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/--
The inverse component of the canonical specified proper compositor is the inverse
component of the ordinary compact-support compositor.
Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
(blueprint: lem-sf-proper-shriek-compositor-supports-refl)
-/
theorem properRouteCompIso_inv_app_eq_canonical {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) [IsProper p] [IsProper f]
    [IsProper (p ≫ f)]
    (E : DerivedCategoryModule A W) :
    (properRouteCompIso A p f (p ≫ f) rfl).inv.app E =
      (rightDerivedLowerShriekCompIso A p f).inv.app E := by
  simp only [properRouteCompIso, rightDerivedLowerShriekCongrIso,
    Iso.trans_inv, Iso.symm_inv, Iso.refl_hom, Category.comp_id]

theorem properRouteCompIso_comp_app_eq_canonical {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) [IsProper p] [IsProper f]
    [IsProper (p ≫ f)]
    (E : DerivedCategoryModule A W) :
    (properRouteCompIso A p f (p ≫ f) rfl).inv.app E ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (p ≫ f)).hom.app E =
      (rightDerivedLowerShriekCompIso A p f).inv.app E ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (p ≫ f)).hom.app E := by
  rw [properRouteCompIso_inv_app_eq_canonical A p f E]

/--
The raw proper forget-supports compositor remains valid when the properness
instance for the composite is made explicit. This is the raw calculation used
by the canonical-composite transport.
Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
(blueprint: lem-sf-proper-shriek-compositor-supports-raw-explicit)
-/
theorem properShriekComp_comp_forgetSupports_raw_with_comp {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) [IsProper p] [IsProper f]
    [IsProper (p ≫ f)] (E : DerivedCategoryModule A W) :
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
