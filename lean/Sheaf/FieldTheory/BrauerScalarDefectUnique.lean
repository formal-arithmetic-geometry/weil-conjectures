/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker H3
-/
module

public import Sheaf.FieldTheory.BrauerScalarDefect

/-!
# Independence of the scalar-defect class for a fixed central simple algebra

Source: Stacks Project, the construction between Tags 03R6 and 03R7, and Tag 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-unique).
-/

@[expose] public section

universe u

namespace Field

/-- Two matrix descent realizations for the same algebra have the same class.

Proof: unpack both realizations into splittings `e`, `e'`, locally constant lifts
`b`, `b'`, and homogeneous cocycles `z`, `z'`. Equality of the dimensions of the
split algebras gives equality of their positive matrix sizes. After reindexing,
Skolem-Noether identifies the change of splitting with conjugation by a fixed
invertible matrix `P`, so that `e'(a) = P⁻¹ * e(a) * P`.
The lifts `d(g) = P⁻¹ * b(g) * g(P)` implement the descent datum for `e'`.
Both `d(g)` and `b'(g)` implement the same automorphism of the full matrix algebra:
the descent identity holds on `e'(1 ⊗ a)`, which spans it over the separable closure.
Their quotient is therefore central, hence uniquely a scalar unit `c(g)`.
The map `g ↦ g(P)` is locally constant: the finitely many entries of `P` lie in a
finite separable extension and its fixing subgroup is open. Thus `d` is locally
constant. Extract `c(g)` from any diagonal entry of `b'(g) * d(g)⁻¹`; positivity
of the size supplies such an entry, and this extraction shows `c` is locally constant.
Substitute `b'(g) = c(g) * d(g)` in the multiplication-defect identities. Cancellation
of `P` and `g(P)` gives `z'(g,h) = c(g) * g(c(h)) * c(gh)⁻¹ * z(g,h)` in
inhomogeneous coordinates. Thus the two cocycles differ by the continuous
one-coboundary of `c`. Convert back to homogeneous cochains by
`q(g₀,g₁) = g₀(c(g₀⁻¹*g₁))`. Its alternating differential is their difference,
and equality of the inhomogeneous values determines an equivariant homogeneous
cochain by evaluating at `(1,g,g*h)`. The homology projection kills that differential.
Use the two equations identifying the homology images with `x` and `y` to conclude.

Source: Stacks Project, scalar-defect independence in the construction following
Lemma 03R6 and preceding Theorem 03R7; the differential of Section 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-unique). -/
theorem brauerScalarDefect_unique (K : Type u) [Field K]
    (A : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K A y) :
    x = y := by sorry

end Field
