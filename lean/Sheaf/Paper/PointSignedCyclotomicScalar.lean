/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.PointSignedCyclotomicActionData

/-! # Scalar action on signed cyclotomic lines

Source: Deligne, Weil I (2.2), pp. 280--281; Weil II (1.1.7), pp. 150--151.
(blueprint: lem-pur-point-signed-section-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointSignedCyclotomicAction

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The restriction/comparison operator on an arbitrary signed section is the
geometric cyclotomic scalar.

Source: Deligne, Weil I (2.2), pp. 280--281; Weil II (1.1.7), pp. 150--151
(blueprint: lem-pur-point-signed-section-scalar).

Proof: Choose a compatible primitive root system in the algebraic closure.
The point-root-coordinate theorem identifies each signed line with its coefficient
ring, with positive generator the prescribed root tensor and negative coordinate
evaluation at the positive generator. The root comparisons identify the restriction
operator on each finite root with inverse field Frobenius. Passing through the root
projections gives multiplication by the inverse of q on the completed root line.
The positiveLineMaps normalization extends this formula over completed coefficients;
the finitePositiveLineMaps normalization gives exactly its finite reduction. Constants
are fixed by restriction and its normalized comparison. Induction on positive powers
therefore multiplies by inverse(q)^d. For a negative degree -d, the signedLineMaps
evaluation equation cancels the positive comparison, so the functional is composed
with the inverse positive action and is multiplied by q^d. In degree zero the map
is the coefficient comparison. Every section is a coefficient multiple of the
normalized generator, and semilinearity becomes coefficient linearity since the
constant comparisons fix coefficients. This proves the formula on all sections,
including finite ramified quotients. The condition l != p makes q a coefficient unit. -/
theorem signed_section_scalar (hl : l ≠ D.p) (a : Option ℕ) (m : ℤ)
    (x : (line D l E a m).val.obj (op (finalObject D))) :
    action D l E a m x =
      scale D l E a m (Ring.inverse (D.q : scalars l E a) ^ m.toNat *
        (D.q : scalars l E a) ^ (-m).toNat) x := by sorry

end WeilConjectures.PointSignedCyclotomicAction
