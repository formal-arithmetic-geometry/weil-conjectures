/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.AlgebraicGeometry.ProperShriekCompSupportsCanonical
import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
import WeilConjectures.AlgebraicGeometry.ProperShriekCompSupportsCanonicalHelper
import WeilConjectures.AlgebraicGeometry.ProperShriekCompSupportsRaw
import WeilConjectures.AlgebraicGeometry.ProperShriekCompCompForgetSupports
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.AlgebraicGeometry.ProperShriekCompSupports

/-! # Proper forget supports and the specified compact-support compositor

Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

private theorem properRouteCompIso_inv_app_eq {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) (h : W ⟶ S) (w : p ≫ f = h)
    [IsProper p] [IsProper f] [IsProper h] (E : DerivedCategoryModule A W) :
    (properRouteCompIso A p f h w).inv.app E =
      (rightDerivedLowerShriekCompIso A p f).inv.app E ≫
        (rightDerivedLowerShriekCongrIso A w).hom.app E := by
  simp only [properRouteCompIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]


private theorem route_refl {W X S : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ S)
    [IsProper p] [IsProper f] :
    properRouteCompIso A p f (p ≫ f) rfl = rightDerivedLowerShriekCompIso A p f := by
  unfold properRouteCompIso rightDerivedLowerShriekCongrIso
  simp

/-- The equality case of the specified compositor is the canonical compositor.
Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
(blueprint: lem-sf-proper-shriek-compositor-supports-refl)
-/
theorem properRouteCompIso_refl {W X S : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ S)
    [IsProper p] [IsProper f] :
    properRouteCompIso A p f (p ≫ f) rfl = rightDerivedLowerShriekCompIso A p f := by
  exact route_refl A p f

end AlgebraicGeometry.Etale
