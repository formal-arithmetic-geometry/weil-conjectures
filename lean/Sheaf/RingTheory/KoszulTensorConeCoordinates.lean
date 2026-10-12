/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.KoszulComplex

/-!
# Coordinates for adjoining the final Koszul generator

Source: Stacks Project, Tags 0628 and 0629.
(blueprint: lem-weil-pbc-koszul-tensor-cone-coordinates).
-/

@[expose] public section

universe u v

namespace ExteriorAlgebra

/-- Source: Stacks Project, Tags 0628 and 0629
(blueprint: lem-weil-pbc-koszul-tensor-cone-coordinates).

Proof: split the exterior-power basis of `R^(r+1)` according to whether its
last generator occurs. Send `(a,b)` to `a + e_last ∧ b`, with the last generator
placed first in the second summand. The resulting basis bijections give linear
isomorphisms in each positive degree; degree zero is the identity on scalars.
Tensor these isomorphisms with `M`. Contraction with the sequence's linear form
restricts to the prefix contraction on the first summand. On the second summand,
the graded Leibniz rule gives `d(e_last ∧ b) = f_last b - e_last ∧ d b`.
This proves both displayed differential formulas, including the separate formula
from degree one to degree zero. When `r=0`, the positive prefix exterior powers
are zero and the same basis argument and formulas still hold. -/
theorem exists_koszulTensorConeCoordinates {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin (r + 1) → R) :
    let A := koszulComplexTensor R r (fun i ↦ f i.castSucc) M
    let B := koszulComplexTensor R (r + 1) f M
    ∃ (e₀ : B.X 0 ≃ₗ[R] A.X 0)
      (e : ∀ n : ℕ, B.X (n + 1) ≃ₗ[R] A.X (n + 1) × A.X n),
      (∀ x : B.X 1, e₀ (B.d 1 0 x) =
        A.d 1 0 (e 0 x).1 + f (Fin.last r) • (e 0 x).2) ∧
      (∀ (n : ℕ) (x : B.X (n + 2)), e n (B.d (n + 2) (n + 1) x) =
        (A.d (n + 2) (n + 1) (e (n + 1) x).1 +
          f (Fin.last r) • (e (n + 1) x).2,
        -A.d (n + 1) n (e (n + 1) x).2)) := by sorry

end ExteriorAlgebra
