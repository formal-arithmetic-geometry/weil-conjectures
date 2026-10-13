/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition

/-! # Termwise representatives in affine spectrum coordinates

Source: Stacks Project, Tags 0DJ8 and 0D5S.
(blueprint: lem-pc-affine-spectrum-coordinate-representatives).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- Spectrum transport can be represented by the actual termwise tensor pullbacks.
This only constructs representatives; it asserts no stalk condition or comparison
invertibility and does not require a base-change square.

Proof: put j = X.isoSpec.inv and j' = X'.isoSpec.inv. Tensor pullback along
these isomorphisms is an exact equivalence: the inverse equivalence is pullback
along the corresponding hom, and the composition and identity isomorphisms
come from the pullback/pushforward adjunctions. In particular it preserves
quasi-isomorphisms, computes derived pullback on every complex, and preserves
K-flatness. Set P0 = j* c.P and N0 = j'* c.N termwise. The universal derived
counits on these exact functors, composed with derived pullback of c.e and c.e',
give isomorphisms Q(P0) to affineSpectrumDerivedObject X K and Q(N0) to
its primed analogue. Naturality of isoSpec identifies
Spec.map g'.appTop followed by j with j' followed by g'. The underived
composition comparison therefore gives a chain isomorphism between
(Spec.map g'.appTop)* P0 and j'* (g'* c.P). Follow it by j'* c.t to define t0.
K-flatness of P0 makes its counit for the spectrum map invertible. The defining
leftDerivedLift equation for both composition comparisons, together with
naturality of the counits and c.represents, shows that t0 represents precisely
(affineSpectrumDerivedPullbackIso g').hom.app K followed by j'^* of phi.
Thus these data are Coordinates for affineSpectrumDerivedMorphism, with the two
stated equalities of complexes. The construction also works for zero complexes
and empty schemes, and needs no boundedness or quasi-coherence.
Source: Stacks Project, Tag 0DJ8, affine reduction, and Tag 0D5S,
composition of derived pullback using termwise K-flat representatives.
(blueprint: lem-pc-affine-spectrum-coordinate-representatives). -/
theorem exists_affineSpectrum_coordinate_representatives
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X) (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (c : Coordinates g' K K' φ) :
    ∃ d : Coordinates (Spec.map g'.appTop)
        (affineSpectrumDerivedObject X K) (affineSpectrumDerivedObject X' K')
        (affineSpectrumDerivedMorphism g' K K' φ),
      d.P = ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.P ∧
      d.N = ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.N := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
