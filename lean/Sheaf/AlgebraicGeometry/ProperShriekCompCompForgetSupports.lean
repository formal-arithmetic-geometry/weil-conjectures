/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper

/-! Compactification-level proper compositor and forget-supports calculation.
Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
(blueprint: lem-sf-proper-shriek-compositor-supports-raw-compactification)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Forget supports commutes with composition on compatible compactifications.
Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, first triangle, common pullback counits.

Proof: expand the compatible compositor into the open/proper exchange, the composition
of open extensions, and the ordinary proper direct-image compositor. Move the open
forget-supports map across exchange using its adjunction-unit mate equation. Composition
of the two open forget-supports maps is the forget-supports map for their composite,
by the composite counit formula and uniqueness of adjoints. Naturality and associativity
of the ordinary direct-image compositor then identify the remaining three proper
pushforward factors with the displayed compositor for p and f. The equality
`e.restrict.i ≫ pullback.fst e.g d.i = e.i` removes the final open congruence.
This calculation has no comparison between different compactifications.
(blueprint: lem-sf-proper-shriek-compositor-supports-raw-compactification)
-/
theorem properShriekComp_compactificationForgetSupports {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) [IsProper p] [IsProper f]
    (d : Compactification f) (e : Compactification (p ≫ d.i))
    (E : DerivedCategoryModule A W) :
    (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom.app E ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A) (d.comp e)).app E =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
          ((compactificationForgetSupports (ModuleCat.{u + 1} A) e.restrict).app E) ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A) d).app
          ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj E) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) p f (p ≫ f) rfl).hom.app E := by
  sorry

end AlgebraicGeometry.Etale
