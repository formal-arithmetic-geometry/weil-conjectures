/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Localization.Defs
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.AffineSpaceOpenInvertibleTrivial

/-! # Triviality of invertible modules on special linear matrix schemes

Source: Milne, Algebraic Groups (2017), Proposition 20.30, printed p.417,
and the scheme product decomposition in 2.42, printed p.53
(blueprint: lem-sfb-special-linear-picard-zero).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Every invertible module on SL_n over any field is isomorphic to the structure sheaf.
Here `LinearGroupSchemes.specialLinear` is precisely Spec of the polynomial matrix
coordinate ring modulo det - 1. Equivalently, its group of isomorphism classes of
invertible modules under tensor product is trivial. No characteristic is excluded.

Source: Milne, Algebraic Groups (2017), Proposition 20.30, printed p.417,
and 2.42, printed p.53 (blueprint: lem-sfb-special-linear-picard-zero).

Proof:
1. Write P = k[x_ij], d = det(x_ij), A = P/(d-1), and B = P[1/d]. The basic
open D(d) in affine n-squared space is G = Spec B by
`lem-weil-pbc-affine-open-section-vanishing-prime` (b). Localization and its inverse
of d are supplied by `def-weil-ring-localization-away`.
2. Polynomial evaluation and `lem-weil-pbc-ring-localization-universal-property`
give q : B -> A, sending every x_ij to its residue and d inverse to 1. In B, divide
the first column of the generic matrix by d. Every Leibniz determinant term contains
exactly one first-column factor, so the resulting determinant is 1, in every
characteristic (`def-weil-pbc-matrix-determinant`). Evaluation descends to s : A -> B
using `def-weil-pbc-mv-polynomial-ring` and `def-weil-pbc-algebra-hom-quotient`.
On every coordinate q composed with s is the identity. Contravariant Spec
(`def-weil-affine-spectrum`) gives j : X -> G and r : G -> X with r composed with
j the identity. This is the retraction underlying Milne 2.42.
3. Pull L back along r using `def-pc-module-pullback`. Pulling back each local
rank-one trivialization from `def-sc-invertible-module` shows r*L is invertible.
The local tensor map a tensor b -> a r-sharp(b), with inverse a -> a tensor 1,
also identifies j*O_G with O_X.
4. Apply `lem-sfb-affine-space-open-invertible-trivial` to r*L on D(d). Pull its
trivialization back along j. The identity and composition comparisons of
`def-pc-module-pullback` and r composed with j = id give
L isomorphic to j*r*L isomorphic to j*O_G isomorphic to O_X. Thus every Picard
class is the unit. For n = 1 this is k[x]/(x-1) isomorphic to k, and the same
retraction works. No field extension or characteristic hypothesis is used. -/
theorem nonempty_iso_unit_specialLinear (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n)
    (L : (LinearGroupSchemes.specialLinear k n).left.Modules) [L.IsInvertible] :
    Nonempty (L ≅ Scheme.Modules.unit (LinearGroupSchemes.specialLinear k n).left) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
