/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import WeilConjectures.AlgebraicGeometry.Modules.Differentials

/-!
# Relative differentials of a smooth morphism have constant rank

Source: Stacks Project, Morphisms of Schemes, Lemma 29.35.12 (Tag 02G1)
(blueprint: lem-sc-smooth-omega-finite-locally-free).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The relative differential sheaf of a smooth morphism of relative dimension `d` is
locally free of constant rank `d`.

Source: Stacks Project, Morphisms of Schemes, Lemma 29.35.12 (Tag 02G1)
(blueprint: lem-sc-smooth-omega-finite-locally-free).

Proof, step 1: fix a point `x` of `X`. Smoothness of relative dimension `d`
(`def-sbc-smooth-morphisms`) gives fibre dimension `d` at `x`. Apply
`lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension` to obtain affine neighbourhoods
`W = Spec A` of `x` and `V = Spec R` of `f(x)`, with `f(W)` contained in `V`, on which
`KaehlerDifferential R A` is free of rank `d`.
Step 2: the affine description of the relative differential sheaf identifies its restriction
on `W` with the sheaf associated to this module, hence with `O_W` to the direct-sum power `d`.
These neighbourhoods cover `X`, so the sheaf is locally free of constant rank `d`, exactly
as in `def-amb-finite-locally-free-module`. -/
theorem isFiniteLocallyFreeOfRank_relativeDifferentials {X S : Scheme.{u}} (f : X ⟶ S)
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) f.relativeDifferentials d := by
  sorry

end AlgebraicGeometry.Scheme.Hom
