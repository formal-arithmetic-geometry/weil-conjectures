/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q104
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Compactification.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.Compactification.Defs

/-!
# Projective compactification of an affine piece

Source: literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/
sk-lem-nagata-sketch-affine-cover/det-nagata-affine-opens-projective.md
(blueprint: det-nagata-affine-opens-projective)

## Main statements

* `AlgebraicGeometry.det_nagata_affine_opens_projective`: the canonical
  scheme-theoretic image of the standard projective-chart immersion of an affine
  finite-type scheme is a dense projective compactification.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The scheme-theoretic image of the canonical affine-space immersion into the
standard projective chart is a dense projective compactification of the original
finite-type morphism.

Source: literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/
sk-lem-nagata-sketch-affine-cover/det-nagata-affine-opens-projective.md
(blueprint: det-nagata-affine-opens-projective)

Proof plan: the canonical affine-space immersion and the standard affine chart are
provided by `Scheme.Hom.affineSpaceImmersion` and
`AffineSpace.toRelativeProjectiveSpace`.  Their composite is an immersion.  Its
scheme-theoretic image has a closed immersion into projective space, and the
canonical factor is a quasi-compact open immersion that is scheme-theoretically
dominant.  Projective space is proper over the base; composing with the closed
immersion gives a proper morphism, while the closed immersion gives the
H-projective presentation.  The resulting data form the compactification
`Compactification`.
-/
theorem det_nagata_affine_opens_projective
    {S U : Scheme.{u}} (f : U ⟶ S) [IsNoetherian S] [IsAffine U]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ c : Compactification f,
      c.Z = (f.affineSpaceImmersion ≫
        AffineSpace.toRelativeProjectiveSpace
          (ULift.{u} (Fin f.affineSpaceImmersionDim)) S).image ∧
      IsClosedImmersion
        ((f.affineSpaceImmersion ≫
          AffineSpace.toRelativeProjectiveSpace
            (ULift.{u} (Fin f.affineSpaceImmersionDim)) S).imageι) ∧
      HEq c.i ((f.affineSpaceImmersion ≫
        AffineSpace.toRelativeProjectiveSpace
          (ULift.{u} (Fin f.affineSpaceImmersionDim)) S).toImage) ∧
      HEq c.g ((f.affineSpaceImmersion ≫
        AffineSpace.toRelativeProjectiveSpace
          (ULift.{u} (Fin f.affineSpaceImmersionDim)) S).imageι ≫
        (ℙ(Option (ULift.{u} (Fin f.affineSpaceImmersionDim)); S) ↘ S)) ∧
      IsOpenImmersion c.i ∧ QuasiCompact c.i ∧
      IsSchemeTheoreticallyDominant c.i ∧ IsProper c.g ∧ IsProjective c.g ∧
      c.i ≫ c.g = f := by
  sorry

end AlgebraicGeometry
