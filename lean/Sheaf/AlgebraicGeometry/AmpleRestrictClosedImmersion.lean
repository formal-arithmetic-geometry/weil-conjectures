/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Modules.TensorPowerSectionNonvanishingPullback

/-! # Ampleness restricts to closed subschemes

Source: Stacks Project, Properties, Tag 01PU (lemma-ample-on-closed)
(blueprint: lem-trf-ample-restrict-closed-immersion).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Source: Stacks Project, Properties, Tag 01PU (lemma-ample-on-closed)
(blueprint: lem-trf-ample-restrict-closed-immersion).
Let `Y` be a scheme and `M` an ample invertible module on `Y`. For every closed
immersion `i : X ⟶ Y`, the tensor pullback of `M` along `i` is ample on `X`.
Proof: put `L = i^* M`. The pullback-invertible theorem gives invertibility of `L`.
Ampleness gives quasi-compactness of `Y`; a closed immersion identifies `X` with a
closed subset, so `X` is quasi-compact. For each point choose the positive tensor
power section supplied by ampleness. Pullback of sections identifies its nonvanishing
locus with the inverse image of the original affine locus. The closed-immersion
affine-cover criterion makes this inverse image affine, completing ampleness of `L`.
The proof uses `lem-weil-pbc-invertible-pullback-invertible`,
`def-weil-pbc-ample-invertible-module`, `def-weil-closed-immersion`,
`lem-weil-pbc-closed-in-quasi-compact`,
`lem-weil-pbc-tensor-power-section-nonvanishing-pullback`, and
`lem-weil-pbc-closed-immersion-affine-cover-criterion`.
-/
theorem isAmple_tensorPullback_of_isClosedImmersion
    {Y : Scheme.{u}} (M : Y.Modules) [M.IsInvertible] (hM : IsAmple Y M)
    {X : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] :
    @IsAmple X ((tensorPullback i).obj M) ((invertible_pullback_tensor i).1 M).2 := by
  sorry

end AlgebraicGeometry.Scheme.Modules
