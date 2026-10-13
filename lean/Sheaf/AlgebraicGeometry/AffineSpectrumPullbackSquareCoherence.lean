/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates
public import Sheaf.AlgebraicGeometry.SchemeDerivedMateEvaluation

/-! # AffineSpectrumPullbackSquareCoherence

Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-affine-spectrum-pullback-square-coherence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The square pullback comparison commutes with forward spectrum coordinates.

Proof: expand q and each forward comparison into c and the equality isomorphisms
for scheme naturality. Naturality of c moves the arbitrary map k to the right;
thus it suffices to compare natural transformations at N. Apply the associativity
law for c to each of the four length-three paths around the commutative prism
whose vertical maps are toSpecGamma. Scheme.toSpecGamma_naturality identifies
its four side faces, and h and h0 identify the bottom and top faces. The equality
isomorphisms are independent of the chosen equality proofs by proof irrelevance.
Cancel adjacent inverse comparisons. Both composites become the comparison for
the same length-three scheme map; hence they agree. No direct image, counit or
base-change mate occurs, and k is arbitrary. Identities and zero objects need
no separate case.
Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-affine-spectrum-pullback-square-coherence). -/
theorem affineSpectrum_pullback_square_coherence
    {X X' S S' : Scheme.{u}}
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (h0 : Spec.map g'.appTop ≫ Spec.map f.appTop =
      Spec.map f'.appTop ≫ Spec.map g.appTop)
    (M : schemeDerivedCategory S) (N : schemeDerivedCategory (Spec Γ(S, ⊤)))
    (k : M ⟶ (derivedPullback S.toSpecΓ).obj N) :
  (derivedPullback f').map
      ((derivedPullback g).map k ≫ (affineSpectrumForwardPullbackIso g).hom.app N) ≫
      (affineSpectrumForwardPullbackIso f').hom.app
        ((derivedPullback (Spec.map g.appTop)).obj N) ≫
      (derivedPullback X'.toSpecΓ).map
        (canonicalDerivedSquareComparison (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) h0 N) =
    canonicalDerivedSquareComparison f f' g g' h M ≫
      (derivedPullback g').map ((derivedPullback f).map k) ≫
      (derivedPullback g').map ((affineSpectrumForwardPullbackIso f).hom.app N) ≫
      (affineSpectrumForwardPullbackIso g').hom.app
        ((derivedPullback (Spec.map f.appTop)).obj N) := by sorry

end AlgebraicGeometry
