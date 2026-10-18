/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Mathlib.Topology.Instances.Matrix

/-!
# Continuous elimination of a unit pivot

Source: the auxiliary elementary calculation in the DAG node
`lem-sfb-unit-pivot-schur-formula`, motivated by Hemo--Richarz--Scholbach,
*Constructible sheaves on schemes*, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula).
The paper supplies the continuous-division context; the matrix calculation is agent-written.

The five constructions below are the prescribed factors and residual block of this one node.
Index `0` is the first index; sizes `n + 1` and `m + 1` cover all positive sizes.
`Ring.inverse` agrees with inversion of units, without assuming global continuity of inversion.
-/

@[expose] public section

universe u v

namespace Matrix

/-- The diagonal factor `L₀ = diag(a⁻¹, 1, …, 1)` in the auxiliary pivot calculation
motivated by HRS, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula). -/
noncomputable def unitPivotScaling {A : Type u} [CommRing A] {n m : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  diagonal (fun i => if i = 0 then Ring.inverse (K 0 0) else 1)

/-- The factor `L₁`, equal to the identity except for `-a⁻¹ Kᵢ₁` below the pivot,
in the auxiliary calculation motivated by HRS, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula). -/
noncomputable def unitPivotLeftElimination {A : Type u} [CommRing A] {n m : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  of (fun i j => if i ≠ 0 ∧ j = 0 then -(Ring.inverse (K 0 0) * K i 0)
    else (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i j)

/-- The prescribed left factor `L = L₀ L₁`, in this order, in the auxiliary calculation
motivated by HRS, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula). -/
noncomputable def unitPivotLeft {A : Type u} [CommRing A] {n m : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  unitPivotScaling K * unitPivotLeftElimination K

/-- The factor `R₀`, equal to the identity except for `-a⁻¹ K₁ⱼ` to the right of the pivot,
in the auxiliary calculation motivated by HRS, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula). -/
noncomputable def unitPivotRightElimination {A : Type u} [CommRing A] {n m : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
  of (fun i j => if i = 0 ∧ j ≠ 0 then -(Ring.inverse (K 0 0) * K 0 j)
    else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) A) i j)

/-- The reduced block `Hᵢⱼ = Kᵢⱼ - a⁻¹ Kᵢ₁ K₁ⱼ` in the auxiliary pivot calculation
motivated by HRS, proof of Theorem 6.12(2), pp. 18--19. Successor indices omit the first row
and column (blueprint: lem-sfb-unit-pivot-schur-formula). -/
noncomputable def unitPivotSchurComplement {A : Type u} [CommRing A] {n m : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (m + 1)) A) : Matrix (Fin n) (Fin m) A :=
  of (fun i j => K i.succ j.succ - Ring.inverse (K 0 0) * K i.succ 0 * K 0 j.succ)

/-- Explicit continuous unit-pivot elimination over a commutative topological ring.
Source: the auxiliary calculation motivated by HRS, proof of Theorem 6.12(2), pp. 18--19
(blueprint: lem-sfb-unit-pivot-schur-formula).

The pointwise `IsUnit` clauses say that the prescribed matrices belong to the general linear
groups, whose elements are exactly the units of square matrix rings. The next four clauses
assert entrywise continuity of the two matrices and their actual inverses. The last two give
continuity of the reduced block and the prescribed block identity.

Proof plan (agent-written auxiliary calculation, not a formula stated in HRS):
1. Put `b = a⁻¹`, `N = L₁ - I`, and `P = R₀ - I`. Only the first column of `N` and the first
   row of `P` can be nonzero, with zero pivot entries. Thus `N² = P² = 0`, so their inverses
   are `I - N` and `I - P`. Matrices and finite-sum multiplication use def-weil-matrix.
2. `D = diag(a, 1, …, 1)` inverts `L₀`, so `(I - N) D` inverts `L = L₀ L₁`.
   Its pivot entry is `a`, entries below it are `Kᵢ₁`, and the other entries are those of `I`.
3. Column elimination gives `(K R₀)ᵢ₁ = Kᵢ₁` and, for `j > 1`,
   `(K R₀)ᵢⱼ = Kᵢⱼ - b Kᵢ₁ K₁ⱼ`. The latter is zero in the first row and is `H` below it.
4. Multiplication by `L₁` kills the first column below the pivot; multiplication by `L₀`
   changes the pivot from `a` to `1`, leaving `H` unchanged. This is the displayed identity.
5. Every entry of the factors, their inverses and `H` is a constant, a given continuous
   entry, or a sum/product/negative of these and the separately continuous `b`.
   Topological-ring operations therefore prove all five entrywise continuity assertions.
6. Empty reduced row/column sets give the one-row/one-column cases; if both are empty the
   identity is `b a = 1`. Empty `T` gives vacuous pointwise statements and continuous maps.
-/
theorem continuous_unitPivot_schur_formula {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] {T : Type v} [TopologicalSpace T]
    {n m : ℕ} (K : T → Matrix (Fin (n + 1)) (Fin (m + 1)) A)
    (hK : ∀ i j, Continuous (fun t => K t i j))
    (hunit : ∀ t, IsUnit (K t 0 0))
    (hinv : Continuous (fun t => Ring.inverse (K t 0 0))) :
    (∀ t, IsUnit (unitPivotLeft (K t))) ∧
    (∀ t, IsUnit (unitPivotRightElimination (K t))) ∧
    (∀ i j, Continuous (fun t => unitPivotLeft (K t) i j)) ∧
    (∀ i j, Continuous (fun t => unitPivotRightElimination (K t) i j)) ∧
    (∀ i j, Continuous (fun t => Ring.inverse (unitPivotLeft (K t)) i j)) ∧
    (∀ i j, Continuous (fun t => Ring.inverse (unitPivotRightElimination (K t)) i j)) ∧
    (∀ i j, Continuous (fun t => unitPivotSchurComplement (K t) i j)) ∧
    (∀ t, unitPivotLeft (K t) * K t * unitPivotRightElimination (K t) =
      of (Fin.cases (Fin.cases 1 (fun _ => 0))
        (fun i => Fin.cases 0 (unitPivotSchurComplement (K t) i)))) :=
  sorry

end Matrix
