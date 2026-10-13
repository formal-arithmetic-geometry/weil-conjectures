/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.FieldTheory.TriangularFieldModelEquations
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Weak regularity of triangular model equations

Source: Stacks Project, proof of Tag 07BV, the successive monic equations, with the
localization presentation of Tag 08JZ
(blueprint: lem-weil-pbc-triangular-field-model-weak-regularity).
-/

@[expose] public section

universe u

namespace FieldTheory

/-- Triangular monic equations after a localization equation form a weakly regular
sequence. This is a statement about arbitrary monic equations, with no extension field.
Source: Stacks Project, Algebra, proof of Tags 07BV and 08JZ
(blueprint: lem-weil-pbc-triangular-field-model-weak-regularity).

Proof:
1. In the polynomial domain over `k`, `h T - 1` is nonzero (its constant coefficient
   as a polynomial in `T` is `-1`), hence multiplication by it is injective.
2. Quotienting by that equation identifies the coefficient ring with `k[X,1/h]`.
   After additionally quotienting by the first `i` monic equations, the whole ring
   is a polynomial ring in the remaining variables over the successive quotient
   `B i = k[X,1/h,Y₀,...,Yᵢ₋₁]/(P₀,...,Pᵢ₋₁)`. This follows by the localization
   presentation and successive quotient isomorphisms, since no earlier equation
   involves a later variable.
3. The next equation is the image of `p i` in `B i[Yᵢ]`, with the still later
   variables adjoined to its coefficient ring. Its leading coefficient is one:
   ring maps preserve monicity. Multiplication by a monic polynomial over any
   commutative ring is injective, by comparing the highest nonzero coefficient
   of a product. Thus it is a nonzerodivisor in the successive quotient.
4. Transport this injectivity through the quotient isomorphisms of step 2. These
   are exactly all the conditions `regular_mod_prev` for a weakly regular sequence.
For `r = 0` only step 1 is needed. A monic constant equation may be `1`, so this
statement deliberately asserts weak regularity only: later quotients may be zero.
No nontriviality of the final quotient is assumed or asserted. -/
theorem triangularFieldModelEquations_isWeaklyRegular
    (k : Type u) [Field k] (d r : ℕ) (h : MvPolynomial (Fin d) k)
    (p : (i : Fin r) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
    (hh : h ≠ 0) (hp : ∀ i, (p i).Monic) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin (d + 1 + r)) k)
      (triangularFieldModelEquations k d r h p) := by sorry

end FieldTheory
