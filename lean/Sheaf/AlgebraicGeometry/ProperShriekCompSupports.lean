/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.ProperSupportedKunnethRoute
import Sheaf.AlgebraicGeometry.ProperShriekCompSupportsRaw
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

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

/-- The specified compact-support compositor transports to the ordinary compositor.
Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, proper comparison in the first triangle;
Stacks Tags 07A7 and 0D6E (blueprint: lem-sf-proper-shriek-compositor-supports).

Proof: unfold properRouteCompIso and substitute h=p;f.
Expand rightDerivedLowerShriekCompIso into the compactification of f, the
compactification of p;f pulled back over its open immersion, and the comparison
with the chosen compactification of p. Move the forget-supports transformation
through this last comparison using
rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar.
The remaining compositor is built from ordinary direct-image composition,
composition of extension by zero, and the open/proper exchange. Each commutes
with forget supports: for the open factor this is naturality of the adjunct
of the identity and the composite counit formula; for the exchange it is
rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app_comp_toLowerStar.
Cancel adjacent inverse compactification comparisons. Associativity of ordinary
direct-image composition leaves exactly the displayed ordinary compositor after
the two proper comparisons. Properness identifies the transformations used here
with the homs of their canonical isomorphisms. This argument has no tensor,
projection formula, coefficient objects other than E, or cartesian square input. -/
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
  sorry

end AlgebraicGeometry.Etale
