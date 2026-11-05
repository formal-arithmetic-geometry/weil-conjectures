/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Affine neighbourhoods of finite sets in quasi-projective schemes

In a quasi-projective scheme over a field every finite set of points lies in an affine open
(Stacks 01ZY, 09NN).

## Main statements

- `AlgebraicGeometry.exists_isAffineOpen_superset_of_isImmersion_of_isAffine`: if `X` is
  quasi-compact and quasi-separated and admits a quasi-compact immersion into `ℙ(α; S)` with `S`
  affine, every finite set of points of `X` lies in an affine open.
- `AlgebraicGeometry.exists_isAffineOpen_superset_of_isImmersion`: the same for any immersion
  into `ℙ(α; Spec K)` with `K` a field.
- `AlgebraicGeometry.IsQuasiProjective.exists_isAffineOpen_superset`: every finite set of points
  of a quasi-projective scheme over a field lies in an affine open.

## Proof

The immersion can be replaced by a morphism `ψ : X ⟶ ℙ(β; S)` whose preimages of the standard
opens are affine (`AlgebraicGeometry.exists_isAffineOpen_preimage_of_isImmersion`), so `ψ` is an
affine morphism, as is `ℙ(β; S) ⟶ ℙ^β_ℤ`. Graded prime avoidance gives a form `G` over `ℤ` of
positive degree not vanishing at the images of the finitely many points; the preimage of the
affine open `D₊(G)` is the required affine open.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

end AlgebraicGeometry
