/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Existence, uniqueness, degree and formula of the Koszul differential

Source: literature/stacks-project/more-algebra.tex, More on Algebra, Definition
Tag 0622 and the paragraph after it (blueprint: lem-weil-pbc-koszul-differential).
-/

@[expose] public section

universe u v

open scoped BigOperators

namespace ExteriorAlgebra

/--
The Koszul differential associated to a linear form exists uniquely and has the
stated degree, explicit formula, and graded derivation property. Source:
Stacks Project, More on Algebra, Definition Tag 0622 and the paragraph after it
(blueprint: lem-weil-pbc-koszul-differential).

Proof, following the six steps of the node:
1. By `lem-weil-pbc-koszul-differential-existence`, take the Mathlib left
   contraction `CliffordAlgebra.contractLeft φ` at the zero quadratic form.
   `contractLeft_one` and `contractLeft_ι_mul` give the unit equation and recursion.
   This is the map Stacks constructs by descending the tensor-algebra derivation.
2. For uniqueness in (i), the difference of two such maps vanishes on 1 and
   satisfies Δ(v * x) = -v * Δ(x). Induction on wedge length makes it vanish on
   every generator product. These span the graded pieces and hence the whole
   exterior algebra by `def-weil-pbc-exterior-algebra`, so linearity gives Δ = 0.
3. Substitute x = 1 in the recursion to obtain D(v) = φ(v) * 1. The degree-zero
   piece is R * 1 and maps to zero. Induct on positive degree: its spanning
   products have the form v * y, and both φ(v) * y and v * D(y) have degree one
   less, using the multiplication of graded pieces in
   `def-weil-pbc-exterior-algebra`; for degree one, D(y) = 0.
4. For the formula, the length-one case is step 3. Apply the recursion to the
   first vector times the remaining product and use the induction hypothesis
   on that product. The minus sign shifts each remaining term's exponent by
   one; the first term has positive sign. The one-based source position is
   i.val + 1, so its source exponent is i.val + 2.
5. For the Leibniz rule, fix y and use linearity to reduce homogeneous x to a
   spanning product, as in `def-weil-pbc-exterior-algebra`. Degree zero follows
   from D(r * 1) = 0 and R-linearity. Write a positive-degree product as v * x'.
   Apply the recursion and the induction hypothesis to x' * y; associativity
   regroups the terms as D(v * x') * y + (-1)^m * (v * x') * D(y).
6. For uniqueness in (iv), apply the Leibniz rule to x = y = 1 in degree zero:
   D'(1) = D'(1) + D'(1), hence D'(1) = 0 by subtraction, in every characteristic.
   Apply it in degree one to a generator v, using D'(v) = φ(v) * 1, to get the
   recursion of (i). Step 2 then gives D' = D.
-/
theorem koszul_differential
    (R : Type u) [CommRing R]
    (E : Type v) [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) :
    ∃ (D : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E),
      D 1 = 0 ∧
      (∀ (v : E) (x : ExteriorAlgebra R E),
        D (ExteriorAlgebra.ι R v * x) =
          algebraMap R (ExteriorAlgebra R E) (φ v) * x -
            ExteriorAlgebra.ι R v * D x) ∧
      (∀ (D' : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E),
        D' 1 = 0 →
        (∀ (v : E) (x : ExteriorAlgebra R E),
          D' (ExteriorAlgebra.ι R v * x) =
            algebraMap R (ExteriorAlgebra R E) (φ v) * x -
              ExteriorAlgebra.ι R v * D' x) → D' = D) ∧
      (∀ (v : E), D (ExteriorAlgebra.ι R v) =
        algebraMap R (ExteriorAlgebra R E) (φ v)) ∧
      (Submodule.map D (⋀[R]^0 E) ≤ ⊥) ∧
      (∀ (n : ℕ),
        Submodule.map D (⋀[R]^(n + 1) E) ≤ ⋀[R]^n E) ∧
      (∀ (n : ℕ) (v : Fin (n + 1) → E),
        D (ExteriorAlgebra.ιMulti R (n + 1) v) =
          ∑ i : Fin (n + 1),
            algebraMap R (ExteriorAlgebra R E)
              (((-1 : R) ^ (i.1 + 2)) * φ (v i)) *
              ExteriorAlgebra.ιMulti R n (v ∘ i.succAbove)) ∧
      (∀ (m : ℕ) (x : ⋀[R]^m E) (y : ExteriorAlgebra R E),
        D ((x : ExteriorAlgebra R E) * y) =
          D (x : ExteriorAlgebra R E) * y +
            algebraMap R (ExteriorAlgebra R E) ((-1 : R) ^ m) *
              (x : ExteriorAlgebra R E) * D y) ∧
      (∀ (D' : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E),
        (∀ (m : ℕ) (x : ⋀[R]^m E) (y : ExteriorAlgebra R E),
          D' ((x : ExteriorAlgebra R E) * y) =
            D' (x : ExteriorAlgebra R E) * y +
              algebraMap R (ExteriorAlgebra R E) ((-1 : R) ^ m) *
                (x : ExteriorAlgebra R E) * D' y) →
        (∀ (v : E), D' (ExteriorAlgebra.ι R v) =
          algebraMap R (ExteriorAlgebra R E) (φ v)) → D' = D) := by
  sorry

end ExteriorAlgebra
