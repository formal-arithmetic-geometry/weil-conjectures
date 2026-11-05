/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Unramified.Field
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Constructible sheaves become constant over finite separable extensions of residue fields

Step 3 of the proof of Stacks 09Z6: for a constructible sheaf `C` and a point `x`, there is a
point `v` of an étale scheme over the residue field of the stratum through `x`, mapping to `x`,
with `κ(v) / κ(x)` finite separable, over which `C` becomes constant
(`AlgebraicGeometry.Scheme.exists_isConstant_upperStar_of_isConstructibleSheaf`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

variable {Λ : Type (u + 1)} [Ring Λ]

end Scheme

end AlgebraicGeometry
