/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Sets.Opens
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Local continuous Smith reduction of integral matrices

Source: Hemo--Richarz--Scholbach, arXiv:2305.18131, Example 3.1 and the proof of
Theorem 6.12(2), finite coefficient extension case. The local constant-cokernel-type
Smith variant is the agent argument recorded in the DAG, rather than a verbatim HRS theorem
(blueprint: lem-sfb-continuous-integral-matrix-local-smith).

The valuation topology on the integer ring is its maximal-ideal-adic topology.
The cokernels below are ordinary algebraic module quotients, with no sheaf structure.
-/

@[expose] public section

universe u v

namespace Padic

/-- Continuous integral matrices with locally constant scalar cokernel type admit a local
Smith reduction by integral invertible matrices whose entries and inverse entries are
continuous. The open cover is indexed by the points, each point lying in its own member.
The fixed rectangular diagonal on each member has increasing nonnegative uniformizer
exponents, including exponent zero, and can have no nonzero entries.

Source: Hemo--Richarz--Scholbach, arXiv:2305.18131, Example 3.1 and the continuous integral
pivot/division argument of Theorem 6.12(2); agent local constant-type Smith variant
(blueprint: lem-sfb-continuous-integral-matrix-local-smith).

Proof: (1) Fix a point and an open neighborhood of constant cokernel type. Apply scalar
Smith form (`lem-sc-dvr-saturation-line-smith-normal-form`,
`Submodule.exists_smith_normal_form_of_le`) to the image, lift its basis to the source,
and complement by a basis of the kernel. The cokernel is a direct sum of a free module
and cyclic modules A/(pi^e). Its free rank and the dimensions of pi^(k-1)P/pi^k P for
k >= 1 determine all positive exponents; the matrix dimensions determine the number of
unit pivots. Hence its complete diagonal type is constant on this neighborhood.
(2) If there are no pivots, the image has rank zero, so all entries vanish. Otherwise,
let e be the least exponent. The two-sided scalar Smith equivalence shows every entry
has valuation at least e and some entry at the chosen point has valuation exactly e.
Move it to the first position by constant row and column permutations, and restrict to
its open valuation-e locus. Every entry is divisible by this pivot throughout the locus.
Division is continuous in the fraction field, and the quotients are integral, so elementary
row and column operations clear the first column and row continuously. Their inverses
use negative coefficients. Divide the pivot by pi^e to obtain a continuous unit u;
multiplication of the first row by u inverse normalizes the pivot to pi^e. The DVR and
unit-times-uniformizer facts are those of `def-weil-l-adic-coefficient-extension`.
Additivity of the free rank and the above residue dimensions shows that the residual
block has the constant cokernel type obtained by removing this pivot.
(3) Induct on min(m,n). Extend the residual changes of bases by the identity on the first
coordinate and compose with the elementary changes. Finite products and their inverses
remain entrywise continuous. (4) Choose the resulting neighborhood at every point to
obtain the open cover. Empty matrix sizes, the zero matrix, no pivots, unit pivots,
and mixed free/torsion cokernels are all included; no condition on the space is used. -/
theorem continuous_integral_matrix_local_smith
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (π : coefficientExtensionIntegers l E)
    (hπ : Ideal.span ({π} : Set (coefficientExtensionIntegers l E)) =
      coefficientExtensionMaximalIdeal l E)
    (Y : Type v) [TopologicalSpace Y] (m n : ℕ)
    (F : Y → Matrix (Fin n) (Fin m) (coefficientExtensionIntegers l E))
    (hF : ∀ (i : Fin n) (j : Fin m),
      @Continuous Y (coefficientExtensionIntegers l E) _
        (coefficientExtensionMaximalIdeal l E).adicTopology (fun y ↦ F y i j))
    (h_type : ∀ y : Y, ∃ W : TopologicalSpace.Opens Y, y ∈ W ∧
      ∀ z ∈ W, Nonempty
        (((Fin n → coefficientExtensionIntegers l E) ⧸ LinearMap.range (F z).mulVecLin) ≃ₗ[
          coefficientExtensionIntegers l E]
        ((Fin n → coefficientExtensionIntegers l E) ⧸ LinearMap.range (F y).mulVecLin))) :
    ∃ W : Y → TopologicalSpace.Opens Y, (∀ y : Y, y ∈ W y) ∧
      ∀ y : Y, ∃
        (L : W y → Matrix.GeneralLinearGroup (Fin n) (coefficientExtensionIntegers l E))
        (R : W y → Matrix.GeneralLinearGroup (Fin m) (coefficientExtensionIntegers l E))
        (r : ℕ) (_hr : r ≤ min m n) (e : Fin r → ℕ)
        (D : Matrix (Fin n) (Fin m) (coefficientExtensionIntegers l E)),
        Monotone e ∧
        (∀ (i : Fin n) (j : Fin m),
          D i j = if h : i.val = j.val ∧ i.val < r then π ^ e ⟨i.val, h.2⟩ else 0) ∧
        (∀ (i j : Fin n),
          @Continuous (W y) (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun z ↦ L z i j)) ∧
        (∀ (i j : Fin n),
          @Continuous (W y) (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun z ↦ (L z)⁻¹ i j)) ∧
        (∀ (i j : Fin m),
          @Continuous (W y) (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun z ↦ R z i j)) ∧
        (∀ (i j : Fin m),
          @Continuous (W y) (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun z ↦ (R z)⁻¹ i j)) ∧
        ∀ z : W y,
          (L z : Matrix (Fin n) (Fin n) (coefficientExtensionIntegers l E)) * F z.val *
            (R z : Matrix (Fin m) (Fin m) (coefficientExtensionIntegers l E)) = D := by
  sorry

end Padic
