/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates

/-! # Compatibility of the canonical spectrum comparisons with base-change mates

Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-affine-spectrum-mate-compatibility).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- The bare base-change mate commutes with the explicitly constructed coordinate
isomorphisms. This only concerns the pulled-back coefficient object, with no chosen
coefficient morphism or second coefficient object.

Proof: let c and i be the comparisons selected by exists_derivedPullbackComposition,
and let a be the adjunctions pinned to their derived counits. The equivalence for
inverse spectrum pullback is built from c and i. The direct-image coordinate iso
is the conjugate of affineSpectrumDerivedPullbackIso, under a(f) composed with the
inverse spectrum equivalence on X and the inverse spectrum equivalence on S
composed with a(f0). Its counit equation is conjugateEquiv_counit. First postcompose
both sides with the inverse direct-image coordinate map and cancel its hom-inverse
pair. Apply the inverse Hom equivalence of a(fprime) to this equation. Expand both
base-change
maps into their square comparison followed by pullback of the counit. Substitute
the conjugate counit equations for f and fprime. Naturality moves the inserted
spectrum equivalence units across the square comparisons. The associativity law
for c, applied to the four spectrum naturality squares, identifies the two square
comparison composites. The unit laws for c and the triangle identities for the
spectrum equivalences cancel the inverse spectrum maps and leave identical
transposes. Injectivity of a(fprime)'s Hom equivalence proves the displayed
identity. The equivalence construction retains the specified counit, so this
calculation uses the actual comparisons defining the data, not arbitrary isos.
It needs only commutativity of the two squares; empty schemes, zero rings and
zero coefficient objects are included in the same categorical calculation.
Source: Stacks Project, Tag 08HY, counit definition of the comparison; Tag 0D5S,
composition and its unit and associativity identities.
(blueprint: lem-pc-affine-spectrum-mate-compatibility). -/
theorem affineSpectrum_baseChange_mate_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (h0 : Spec.map g'.appTop ≫ Spec.map f.appTop =
      Spec.map f'.appTop ≫ Spec.map g.appTop)
    (K : schemeDerivedCategory X) :
    schemeDerivedBaseChangeMap f f' g g' h K ≫
        (affineSpectrumDerivedDirectImageIso f').hom.app ((derivedPullback g').obj K) =
      (affineSpectrumBaseChangeSourceIso f g).hom.app K ≫
        (derivedPullback S'.toSpecΓ).map
          (schemeDerivedBaseChangeMap (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) h0
              (affineSpectrumDerivedObject X K) ≫
            (schemeDerivedDirectImage (Spec.map f'.appTop)).map
              ((affineSpectrumDerivedPullbackIso g').hom.app K)) := by sorry

end AlgebraicGeometry
