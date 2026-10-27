/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.FormalTaylorJetMatrices
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Regular jet matrices and their minor ideals

Source: Bierstone--Milman, Invent. Math. 128 (1997), Definitions 7.9,
7.12--7.13, Theorem 7.14 and Remarks 9.1, 9.5.
(blueprint: def-trf-regular-jet-matrix).

The shared exponent, factorial and finite-minor constructions are reexported
from their unique owner `FormalTaylorJetMatrices`. The regular constructions
below retain the declarations previously published in `FormalHilbertStratumMinors`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace AlgebraicGeometry.HilbertCoefficient

open Classical in
/-- Iterate the canonical regular coordinate derivations, with the same order as formal partials.

Source: Bierstone--Milman, Invent. Math. 128 (1997), Definitions 7.9, 7.12--7.13,
Theorem 7.14 and Remarks 9.1, 9.5 (blueprint: lem-trf-formal-hilbert-stratum-minors). -/
def regularIteratedPartial {σ : Type v} [Fintype σ] {B : Type u} [CommRing B]
    (D : σ → Derivation ℤ B B) (δ : σ →₀ ℕ) (h : B) : B :=
  (Finset.univ.toList.flatMap fun j : σ ↦ List.replicate (δ j) j).foldl
    (fun g j ↦ D j g) h

open Classical in
/-- The regular Taylor matrix, using coordinate derivatives divided by multi-index factorials.

Source: Bierstone--Milman, Invent. Math. 128 (1997), Definitions 7.9, 7.12--7.13,
Theorem 7.14 and Remarks 9.1, 9.5 (blueprint: lem-trf-formal-hilbert-stratum-minors). -/
def regularJetMatrix {σ : Type v} [Fintype σ] {k B : Type u} [Field k] [CommRing B]
    (c : MvPolynomial σ k →+* B) (D : σ → Derivation ℤ B B)
    {s : ℕ} (h : Fin s → B) (t : ℕ) :
    Matrix ↥(jetExponents σ t) (Fin s × ↥(jetExponents σ t)) B :=
  fun δ iη ↦ if iη.2.val ≤ δ.val then
    c (MvPolynomial.C ((multiFactorial k (δ.val - iη.2.val))⁻¹)) *
      regularIteratedPartial D (δ.val - iη.2.val) (h iη.1)
  else 0

open Classical in
/-- Regular rank minors with the rank frozen at the specified distinguished point.

Source: Bierstone--Milman, Invent. Math. 128 (1997), Definitions 7.9, 7.12--7.13,
Theorem 7.14 and Remarks 9.1, 9.5 (blueprint: lem-trf-formal-hilbert-stratum-minors). -/
def regularJetMinorIdeal {σ : Type v} [Fintype σ] {k B L : Type u}
    [Field k] [CommRing B] [Field L] (c : MvPolynomial σ k →+* B)
    (D : σ → Derivation ℤ B B) {s : ℕ} (h : Fin s → B) (ev : B →+* L) (t : ℕ) :
    Ideal B :=
  finiteMinorIdeal (regularJetMatrix c D h t)
    (Matrix.rank (fun δ iη ↦ ev (regularJetMatrix c D h t δ iη)) + 1)

end AlgebraicGeometry.HilbertCoefficient
