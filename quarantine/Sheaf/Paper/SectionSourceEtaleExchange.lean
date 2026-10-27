/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H7
-/
module

public import Sheaf.Paper.SectionCompactSourceMaps

/-! # A component of section compact-source exchange

Source: blueprint rank-one Thom proof, Step 3; Stacks Tags 0F7F and 0D6E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SectionCompactSource
variable (A : Type (u + 1)) [CommRing A]

/-- The étale component of the section exchange.  This is the proper/open
normalization and the closed-section base-change mate from Step 3 of the blueprint.
Source: Stacks Tags 0F7F and 0D6E (blueprint: lem-pur-section-source-etale-exchange).
Proof: put q = s followed by the open immersion of c. It is a section of the
proper projection of c, hence closed and proper. Do the same after base change.
Exact closed direct image identifies the degree-zero supported constant with
its derived direct image. Proper/open interchange identifies extension by zero
of that supported constant with direct image along q. Postcompose with the
inverse direct-image compositor for q and the proper projection, and with the
identity direct-image comparison. This composite is etaleSource inverse.
Naturality of the projection exchange and proper/open base-change coherence
identify exchange of this composite with the pasted exchanges for q and the
projection. The mate-pasting law identifies the pasted exchange with exchange
for their composite, which is the identity map of the base. The identity mate
is the scalar-preserving constant pullback by the adjunction triangle identity.
Cancel the two inverse source maps to get precisely the displayed equation.
The reasoning is unchanged on empty schemes and requires no finiteness on B'. -/
theorem etale_section_exchange_component [Finite A]
    {B X B' X' : Scheme.{u}} {h : X ⟶ B} {h' : X' ⟶ B'}
    {v : X' ⟶ X} {g : B' ⟶ B} (sq : IsPullback v h' h g)
    (c : Compactification h) (s : B ⟶ X) (s' : B' ⟶ X')
    [IsClosedImmersion s] [IsClosedImmersion s']
    (hs : s ≫ h = 𝟙 B) (hs' : s' ≫ h' = 𝟙 B')
    (sqS : ChosenCartesianSquare g s' s v) :
    (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.map
        (etaleSource A c s hs).hom ≫
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c).app
        (etaleSupported A s) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map (etaleBeta A sqS) =
    (constantPull A g).hom ≫ (etaleSource A (c.ofIsPullback sq) s' hs').hom := by
  sorry

end AlgebraicGeometry.SectionCompactSource
