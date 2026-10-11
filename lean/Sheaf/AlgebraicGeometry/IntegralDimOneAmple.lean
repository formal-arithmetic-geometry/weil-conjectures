/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.Ample

/-! # Ample invertible modules on integral curves

Source: Stacks Project, Varieties, Lemma 09ND
(varieties-lemma-dim-1-noetherian-integral-separated-has-ample).
(blueprint: lem-sc-integral-dim-one-ample).
-/

universe u

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- An integral Noetherian separated curve has an ample invertible module.
Source: Stacks Project, Varieties, Lemma 09ND.

Proof:
1. Choose a finite cover by nonempty affine opens; each complement is finite
   by `lem-sc-affine-complement-finite-on-integral-curve`.
2. Apply `lem-sc-find-globally-generated` to each affine open and its finite
   complement, obtaining a globally generated invertible module and a section
   with affine principal open equal to that open. The complement points have
   Noetherian local rings of dimension one: they are not the generic point of
   the integral curve, and their local dimensions are at most `dim Y = 1`.
3. The ample criterion `lem-sc-enough-globally-generated-ample` applied to
   these principal opens gives an ample invertible module.
(blueprint: lem-sc-integral-dim-one-ample)
-/
theorem exists_isAmple_of_integral_dim_one
    (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    [Y.IsSeparated]
    (hY : topologicalKrullDim Y = (1 : WithBot ℕ∞)) :
    ∃ L : Y.Modules, ∃ hL : L.IsInvertible, @IsAmple Y L hL := by
  sorry

end AlgebraicGeometry.Scheme.Modules
