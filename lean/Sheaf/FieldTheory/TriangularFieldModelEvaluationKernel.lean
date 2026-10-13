/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.FieldTheory.TriangularFieldModelEquations
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Polynomial.Monic

/-!
# The evaluation kernel of a triangular algebraic tower

Source: Stacks Project, Algebra, proof of Tag 07BV, first assertion, and the
localization presentation of Tag 08JZ
(blueprint: lem-weil-pbc-triangular-field-model-evaluation-kernel).
-/

@[expose] public section

universe u v

namespace FieldTheory

/-- Any finite family in a field algebraic over `k(x)` has triangular monic relations
whose ideal is exactly the kernel of evaluation. The family need not generate `K`.
Source: Stacks Project, proof of Tag 07BV (lemma-colimit-syntomic), the minimal
polynomial construction and denominator clearing; Tag 08JZ
(localization presentation), the kernel of that presentation
(blueprint: lem-weil-pbc-triangular-field-model-evaluation-kernel).

Proof:
1. Let `F = k(x)` inside `K`. Algebraic independence embeds `k[X]` in `F`,
   which is its fraction field. The transcendence basis makes every `b i`
   algebraic over `F`. Set `L_i = F(b j : j < i)`; do not identify `L_m` with `K`.
2. The minimal polynomial of `b i` over `L_i` is monic, of positive degree `e_i`.
   The simple-extension quotient isomorphism and its power basis, followed by
   `Basis.smulTower`, give the bounded products of preceding `b j` as an `F`-basis
   of `L_i`. Expand the coefficients of the minimal polynomial in this basis and
   replace `b j` by `Y_j`, obtaining a monic triangular polynomial over `F`.
3. Express the finitely many `F`-coefficients of all these polynomials as fractions
   in `k[X]`. Let `h` be the product of their nonzero denominators (one if there
   are none). All coefficients lie in `D = k[X,1/h]`. Lift each coefficient
   `a/h^n` to `a(X) T^n`; lift the leading coefficient as exactly one. This gives
   the asserted monic `p i`. Define `y` on the first `d` variables by `x`, on
   variable `d` by `(h(x))⁻¹`, and on variable `d+1+i` by `b i`.
4. The localization quotient identifies `k[X,T]/(hT-1)` with `D`. Quotienting
   further by the lifted `p i` gives `B = D[Y]/(P_i)`, and evaluation kills the
   displayed list of equations.
5. Iterated monic division gives `B` a `D`-basis of the monomials with exponents
   below `e_i`, using the monic quotient power basis and `Basis.smulTower`.
   Their evaluations are the `F`-basis of `L_m` from step 2. Since `D` embeds in
   `F`, an element of `B` evaluating to zero has all its basis coefficients zero.
   Thus evaluation from `B` is injective: a polynomial evaluates to zero exactly
   when it belongs to the displayed ideal, which proves the kernel equality.
For `m = 0` use `h = 1`, the empty polynomial family, and evaluation at `T = 1`.
For `d = 0` the coefficient fraction field is `k`. Repeated generators give
linear minimal polynomials; inseparability does not affect monic division or
power bases. No fraction representation for all of `K` is asserted. -/
theorem exists_triangularFieldModel_evaluation_kernel
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (d : ℕ) (x : Fin d → K) (hx : IsTranscendenceBasis k x)
    (m : ℕ) (b : Fin m → K) :
    ∃ (h : MvPolynomial (Fin d) k)
      (p : (i : Fin m) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
      (y : Fin (d + 1 + m) → K),
      h ≠ 0 ∧ (∀ i, (p i).Monic) ∧
      (∀ j : Fin d, y ⟨j.val, by omega⟩ = x j) ∧
      y ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹ ∧
      (∀ i : Fin m, y ⟨d + 1 + i.val, by omega⟩ = b i) ∧
      RingHom.ker (MvPolynomial.aeval y).toRingHom =
        Ideal.ofList (triangularFieldModelEquations k d m h p) := by sorry

end FieldTheory
