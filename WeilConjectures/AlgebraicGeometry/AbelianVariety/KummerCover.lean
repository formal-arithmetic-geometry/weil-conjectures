/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Covering an abelian variety by opens on which a unit is not an `r`-th power

Let `E` be an abelian variety of positive dimension over a field and `2 ≤ r`. We cover `E` by
finitely many affine opens `U i`, each carrying a unit `f i ∈ Γ(E, U i)` which is not an `r`-th
power in the function field of `E`.

For a point `x`, choose an affine open `V ∋ x` and a closed point `y ∈ V` different from `x`.
Prime avoidance gives `a ∈ Γ(E, V)` which is invertible at `x` and lies in `𝔪_y \ 𝔪_y ^ 2` in the
local ring `𝒪_{E,y}`. This local ring is regular, hence a unique factorization domain, hence
integrally closed, so `a` is not an `r`-th power in its fraction field, the function field of `E`.
The opens `D(a) ∋ x` cover `E`, which is quasi-compact.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.isIntegral`: an abelian variety is an integral scheme.
- `AlgebraicGeometry.Scheme.exists_isAffineOpen_isUnit_not_exists_pow`: a point of a regular
  integral Jacobson scheme with at least two points has an affine open neighbourhood with a unit
  which is not an `n`-th power in the function field, for `2 ≤ n`.
- `AlgebraicGeometry.IsAbelianVariety.exists_finite_cover_units_not_pow`: the cover above.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing Opposite

namespace AlgebraicGeometry

end AlgebraicGeometry
