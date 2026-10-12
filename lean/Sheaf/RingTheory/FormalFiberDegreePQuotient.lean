/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Base change of a simple degree-p field presentation

Source: Stacks Project, More on Algebra, Tag 07PR, binomial presentation paragraph.
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- Base change of a simple degree-p field presentation at its specified coefficient.
Source: Stacks Project, More on Algebra, Tag 07PR, binomial presentation paragraph.
(blueprint: new-lem-weil-pbc-degree-p-quotient-component)

Proof: The element z generates L over M, and its degree is p. The monic polynomial
X^p - a vanishes at z and has degree p, so it is the minimal polynomial of z.
Evaluation therefore identifies M[Z]/(Z^p-a) with L as an M-algebra. Tensor this
presentation over M with R = M tensor_K F. Polynomial base change and quotient
base change identify its source with R[Z]/(Z^p-i(a)), where i(a) = a tensor 1.
Tensor associativity identifies the target L tensor_M R with L tensor_K F.
Compose these algebra equivalences and forget their algebra structure.
This argument also holds when F is zero: both sides are zero rings. -/
theorem FormalFiberDegreePQuotient
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L)
    (F : Type u) [CommRing F] [Algebra K F]
    (p : ℕ) [Fact p.Prime] (z : L)
    (hz : IntermediateField.adjoin M ({z} : Set L) = ⊤)
    (a : M) (ha : z ^ p = (a : L)) (hdeg : Module.finrank M L = p) :
    Nonempty ((Polynomial (TensorProduct K M F) ⧸
      Ideal.span ({Polynomial.X ^ p - Polynomial.C
        (Algebra.TensorProduct.includeLeftRingHom a)} :
          Set (Polynomial (TensorProduct K M F)))) ≃+* TensorProduct K L F) := by
  sorry

end MvPowerSeries
