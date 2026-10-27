/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet

/-!+# Quotient Jacobian minors of linear combinations

Source: Stacks Project, Curves, Tag 0C4B, lemma-fitting-ideal-well-defined,
generator-change paragraph; Algebra, Tag 0F0K, item-cauchy-binet
(blueprint: lem-trf-formal-jacobian-generator-minor-expansion).
-/

@[expose] public section

universe u

set_option autoImplicit false

open scoped BigOperators

namespace MvPowerSeries

open Classical in
/-- Differentiation of linear combinations, their quotient Jacobian product identity,
and the Cauchy--Binet expansion of each selected minor, with increasing index order.
Source: Stacks Project, Curves, Tag 0C4B, generator-change paragraph;
Algebra, Tag 0F0K, item-cauchy-binet
(blueprint: lem-trf-formal-jacobian-generator-minor-expansion).

The new list is written explicitly as `fun a ↦ ∑ b, C a b * f b`; each quotient
Jacobian has list entries as rows and variables as columns. Neither list must generate `I`.

Proof: (1) The formal partial derivative [def-trf-formal-power-series-partial-derivative]
is an F-derivation [def-weil-pbc-kahler-differentials]. Apply additivity to the finite
sum and the Leibniz rule to each product; commute the factors in the error term.
(2) Apply the quotient homomorphism. Since every `f b` lies in `I`, each derivative
of a coefficient times `f b` becomes zero. The remaining sum is the corresponding
entry of the matrix product [def-weil-matrix].
(3) Select the rows of the coefficient matrix using `A.orderEmbOfFin hA` and the
columns of the original Jacobian using `B.orderEmbOfFin hB` [def-weil-submatrix].
Their product is the selected minor of the new Jacobian by (2). Apply
[lem-weil-pbc-cauchy-binet] with sizes `r` and `s`. Its increasing enumeration of
each `S` gives exactly the two submatrices in the summand below.
(4) For `r = 0`, empty determinants are one [def-weil-pbc-matrix-determinant], and
there is one zero-element subset. For `s < r`, the sum has no terms and is zero.
If `r > l` or `r > n`, the required selections `A`, `B` do not exist. The sum and
product-rule calculation also includes `s = 0`, and no characteristic restriction is used.
-/
theorem formalJacobian_generator_minor_expansion (F : Type u) [Field F] (n s l : ℕ)
    (I : Ideal (MvPowerSeries (Fin n) F)) (f : Fin s → MvPowerSeries (Fin n) F)
    (hf : ∀ b : Fin s, f b ∈ I) (C : Matrix (Fin l) (Fin s) (MvPowerSeries (Fin n) F)) :
    (∀ (a : Fin l) (i : Fin n),
      pderiv F i (∑ b : Fin s, C a b * f b) =
        (∑ b : Fin s, C a b * pderiv F i (f b)) +
          ∑ b : Fin s, pderiv F i (C a b) * f b) ∧
    (Matrix.of (fun a i ↦ Ideal.Quotient.mk I (pderiv F i (∑ b : Fin s, C a b * f b))) =
      C.map (Ideal.Quotient.mk I) *
        Matrix.of (fun b i ↦ Ideal.Quotient.mk I (pderiv F i (f b)))) ∧
    (∀ (r : ℕ) (A : Finset (Fin l)) (B : Finset (Fin n))
      (hA : A.card = r) (hB : B.card = r),
      (Matrix.submatrix
        (Matrix.of (fun a i ↦ Ideal.Quotient.mk I
          (pderiv F i (∑ b : Fin s, C a b * f b))))
        (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det =
        ∑ S : {S : Finset (Fin s) // S.card = r},
          ((C.map (Ideal.Quotient.mk I)).submatrix
            (A.orderEmbOfFin hA) (S.val.orderEmbOfFin S.property)).det *
          (Matrix.submatrix
            (Matrix.of (fun b i ↦ Ideal.Quotient.mk I (pderiv F i (f b))))
            (S.val.orderEmbOfFin S.property) (B.orderEmbOfFin hB)).det) := by
  sorry

end MvPowerSeries
