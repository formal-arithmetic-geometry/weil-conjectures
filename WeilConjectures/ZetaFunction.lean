/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

@[expose] public section

/-!
# The zeta function of a scheme

In this file we define the (Hasse-Weil) zeta function of an arbitrary scheme `X` in
maximal generality: it is the Euler product

`ζ_X(s) = ∏ (1 - #κ(x) ^ (-s))⁻¹`

taken over all points `x : X` whose residue field `κ(x)` is finite. The product is
interpreted as an unconditional infinite product (`tprod`), which takes the junk value `1`
whenever the family is not multipliable, so no convergence or finiteness hypotheses on `X`
are needed for the definition.

Every point with finite residue field is a closed point of every affine open containing it
(a finite integral domain is a field), hence a closed point of `X`. Conversely, if `X` is
locally of finite type over `Spec ℤ`, every closed point of `X` has finite residue field by
the general Nullstellensatz. Hence for such `X` (e.g. any variety over a finite field, or
any arithmetic scheme) the product ranges exactly over the closed points of `X` and recovers
the classical arithmetic zeta function; in this case it converges for `re s` large.

## Main definitions

- `AlgebraicGeometry.Scheme.finitePoints`: the points of `X` with finite residue field.
- `AlgebraicGeometry.Scheme.pointNorm`: the norm `N(x) = #κ(x)` of a point.
- `AlgebraicGeometry.Scheme.eulerFactor`: the local factor `(1 - N(x) ^ (-s))⁻¹`.
- `AlgebraicGeometry.Scheme.zeta`: the zeta function `ζ_X(s)` of a scheme `X`.

## Main statements

Basic properties of `finitePoints` and `pointNorm` are proved here. See
`WeilConjectures.ClosedPoints` for the identification of the finite-residue
points with the closed points, `WeilConjectures.Convergence` for the
convergence of the Euler product on a right half-plane for schemes of finite type over
`ℤ`, and `WeilConjectures.SpecialValues` for the computation of the zeta
functions of `Spec 𝔽_q` and `Spec ℤ` (the latter being the Riemann zeta function).

## References

- [J.-P. Serre, *Zeta and L functions*][serre1965]
-/

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The points of a scheme with finite residue field. Any such point is closed in every
affine open containing it, hence closed in `X`. If `X` is locally of finite type over `ℤ`,
these are exactly the closed points of `X` (see `finitePoints_eq_closedPoints`). -/
def finitePoints : Set X :=
  {x | Finite (X.residueField x)}

lemma mem_finitePoints {x : X} : x ∈ X.finitePoints ↔ Finite (X.residueField x) :=
  Iff.rfl

/-- The norm of a point `x` of a scheme is the cardinality of its residue field,
with junk value `0` if the residue field is infinite. -/
noncomputable def pointNorm (x : X) : ℕ :=
  Nat.card (X.residueField x)

end AlgebraicGeometry.Scheme
