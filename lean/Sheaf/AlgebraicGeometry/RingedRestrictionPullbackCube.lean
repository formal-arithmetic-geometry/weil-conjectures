/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.RingedRestrictionOpenCube
public import Sheaf.AlgebraicGeometry.RingedExchangeChainUnit

/-! # The ordinary inverse-image cube for restriction

Source: Stacks Project, sites.tex Tag 03CB and proetale.tex Tag 09A5.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

/-- The six canonical module inverse-image squares commute around an open cube.
Source: Stacks Project, sites.tex Tag 03CB, composition of morphisms of sites,
and proetale.tex Tag 09A5, morphisms of pro-etale sites; step 7 of
lem-sf-ringed-restriction-exchange-open-descent.
(blueprint: lem-sf-ringed-restriction-pullback-cube).
Proof: expand each exchangeModuleSquare as the inverse compositor for its first
path followed by the compositor for its second path. All paths have the same
composite scheme map, by the Cartesian-square commutativity equations.
The coefficient coherence equations of the four side faces, r and C.localRings
identify the composite coefficient isomorphisms. Conjugate the ordinary compositors under
the composite module adjunctions. By exchangeModuleComposition_existsUnique,
their conjugates act on sections by the fibre-product pasting maps. The two
threefold pastings preserve all three projections, so the universal property
of the iterated fibre product identifies them. Faithfulness on module sections
and injectivity of adjunction conjugation give the compositor associativity
with these coefficient transports. Cancel the inverse pairs on the two routes
to obtain the displayed equation. The argument uses neither openness nor any
nonemptiness hypothesis, and applies to zero modules and empty schemes. -/
theorem restriction_pullback_cube
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j)
    (M : proEtaleRingModules Y r.RY) :
    (targetPull C.localRings).map (C.baseFace.exchangeModuleSquare.hom.app M) ≫
        C.targetFace.exchangeModuleSquare.hom.app ((basePull r).obj M) ≫
        (upperPull C.targetFace).map (r.exchangeModuleSquare.hom.app M) =
      C.localRings.exchangeModuleSquare.hom.app ((basePull C.sourceFace).obj M) ≫
        (upperPull C.localRings).map (C.sourceFace.exchangeModuleSquare.hom.app M) ≫
        C.upperFace.exchangeModuleSquare.hom.app ((verticalPull r).obj M) := by sorry

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
