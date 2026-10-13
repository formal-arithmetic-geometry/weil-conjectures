/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.FieldTheory.TriangularFieldModelEquations
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Triangular presentations inside finitely generated fields

Source: Stacks Project, proof of Tag 07BV (the first assertion), using the presentation
from Tag 08JZ (blueprint: lem-weil-pbc-triangular-field-model-presentation).
-/

@[expose] public section

universe u v

namespace FieldTheory

/-- The tower of minimal polynomials gives a triangular presentation embedded in `K`,
whose elements give all fractions in `K`. This asserts no regularity of the equations.
Source: Stacks Project, Algebra, proof of Tag 07BV, with the presentation of Tag 08JZ
(blueprint: lem-weil-pbc-triangular-field-model-presentation).

Proof:
1. Put `F = k(x)`; algebraic independence embeds `k[X]` into `K`. The transcendence
   basis makes `K/F` algebraic. Choose the finite generating family `b` supplied by
   `hfg`, and form the fields `F(b₀,...,bᵢ₋₁)`. The last is `K`.
2. The minimal polynomial of each `bᵢ` is monic of positive degree. The quotient
   isomorphism for a simple algebraic extension and its power basis, iterated with
   `Basis.smulTower`, give the bounded monomials in the `bᵢ` as an `F`-basis of `K`.
3. Expand the coefficients of each minimal polynomial in the preceding monomial
   basis. Replacing `bⱼ` by `Yⱼ` gives triangular monic polynomials over `F`.
4. Write their finitely many coefficients as fractions in `k[X]`. Their denominator
   product `h` is nonzero. All coefficients lie in `D = k[X,1/h]`. Lift each coefficient
   `a/h^j` to `a T^j` without altering the leading coefficient one, giving `p i`.
5. The equations `h T - 1` and the `p i` present
   `B = D[Y]/(P₀,...,Pᵣ₋₁)`: the localization presentation has kernel `(h T - 1)`,
   and quotienting further by the lifts of the `P i` gives precisely `B`.
6. Successive monic division gives `B` a `D`-basis of bounded monomials. Evaluation
   sends this basis to the `F`-independent monomials of step 2. Since `D` embeds in
   `F`, evaluation is injective, giving the required map from the presented quotient.
7. Expand any `z : K` in the `F`-basis and take a common nonzero denominator in
   `k[X]` for its finitely many coefficients. The resulting numerator belongs to `B`,
   as does the denominator, and evaluation gives `z = ι a * (ι s)⁻¹`. The denominator
   remains nonzero since `k[X]` embeds in `F` and hence in `K`.
The empty tower uses `h = 1` and an empty family `p`; `d = 0` uses `k[X] = k`.
No separability is used, so the construction also applies to inseparable extensions. -/
theorem exists_triangularFieldModel_presentation
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (hfg : ∃ (m : ℕ) (b : Fin m → K), IntermediateField.adjoin k (Set.range b) = ⊤)
    (d : ℕ) (x : Fin d → K) (hx : IsTranscendenceBasis k x) :
    ∃ (r : ℕ) (h : MvPolynomial (Fin d) k)
      (p : (i : Fin r) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k)),
      h ≠ 0 ∧ (∀ i, (p i).Monic) ∧
      let A := MvPolynomial (Fin (d + 1 + r)) k ⧸
        Ideal.ofList (triangularFieldModelEquations k d r h p)
      ∃ (ι : A →ₐ[k] K), Function.Injective ι ∧
        ∀ z : K, ∃ a s : A, s ≠ 0 ∧ z = ι a * (ι s)⁻¹ := by sorry

end FieldTheory
