/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
/-! # Stalk condition under affine spectrum coordinates

Source: Stacks Project, Tag 0DJ8, affine spectrum reduction, and Tag 0DJ9.
(blueprint: lem-pc-affine-spectrum-stalk-condition).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical coefficient transport preserves and reflects the single-complex
stalk condition. This conclusion concerns only stalk comparisons, not direct image.

Proof: isoSpec identifies every point z of X' with z0 in Spec Gamma(X'). Naturality
of isoSpec identifies all four stalk ring maps, hence their tensor-to-stalk map.
Tensor pullback along the inverse isomorphisms is exact and takes a K-flat complex
P representing K to a K-flat complex P0 representing the explicitly constructed
coordinate object. Likewise transport N and t representing K' and phi. The
composition counits identify the transported chain map with
`affineSpectrumDerivedMorphism`, since its defining comparison is the universal
left-derived composition comparison. The exact module-stalk functor commutes with
cohomology; the induced ring isomorphisms identify scalar extension and the two
base-derived-tensor model counits. Consequently the stalk comparison at z in these
transported coordinates is conjugate to the original comparison by isomorphisms
on source and target. IsIso is invariant under this conjugation. Coordinate
invariance on each fixed square lets us replace these transported representatives
by arbitrary coordinates. Every point is in the image of isoSpec, and inverse
transport gives the reverse implication. This also covers empty schemes, the zero
complex and arbitrary unbounded complexes; neither boundedness nor flatness of
the square is assumed.
Source: Stacks Project, Tags 0DJ8 and 0DJ9, affine reduction, with the tensor-stalk
identification of Tag 0098 and composition of derived pullback of Tag 0D5S.
(blueprint: lem-pc-affine-spectrum-stalk-condition). -/
theorem affineSpectrumCoordinates_stalkCondition
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') :
    SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ ↔
      SingleComplexBaseChange.StalkCondition
        (Spec.map f.appTop) (Spec.map f'.appTop)
        (Spec.map g.appTop) (Spec.map g'.appTop) sq0
        (affineSpectrumDerivedObject X K) (affineSpectrumDerivedObject X' K')
        (affineSpectrumDerivedMorphism g' K K' φ) := by sorry

end AlgebraicGeometry
