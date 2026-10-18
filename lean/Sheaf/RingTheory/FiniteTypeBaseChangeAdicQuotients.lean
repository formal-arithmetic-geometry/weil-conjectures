/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.Ideal

/-! # Adic quotients after base change to a local completion

Source: Stacks Project, algebra.tex, Tags 00MA(3), 05GG, 05GI and 00CT; the explicit
finite-type localization calculation of the DAG node
(blueprint: lem-trf-finite-type-base-change-adic-quotients).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u v

namespace RingTheory

/-- Base change to the completion of a Noetherian local base preserves the positive adic
quotients of a finite-type localization, compatibly with every quotient transition.
The exponent `n + 1` ranges over exactly the positive integers. The value on every
representative specifies that each equivalence is induced by the canonical local map.

Source: Stacks Project, algebra.tex, Tags 00MA(3), 05GG, 05GI and 00CT; the explicit
finite-type localization and quotient calculation of the DAG node.

Proof:
1. By Noetherianity the maximal ideal of `R` is finitely generated. Apply
   `lem-weil-pbc-adic-completion-mod-power` to obtain the surjective projection from
   the completion to `R / m^n`, with kernel `m^n` extended to the completion. By
   `lem-weil-pbc-local-completion-local-ring` its maximal ideal is the extension of `m`.
2. Since `m C ≤ q`, the structural map to `C / q^n` factors through `R / m^n`.
   Compose with the completion projection. The tensor universal property
   (`def-weil-pbc-module-tensor-product`) gives a ring map from the tensor product
   to `C / q^n`, inverse on the left to the canonical map on quotients.
3. For each element of the completion choose a representative in `R` modulo `m^n`.
   Their difference is in the extended `m^n`, so balancing identifies each pure tensor
   modulo `q^n` with one coming from `C`. Pure tensors generate; the two quotient maps
   are inverse. This uses `lem-weil-pbc-adic-completion-mod-power` and the tensor
   universal property `def-weil-pbc-module-tensor-product`.
4. At exponent one, the quotient comparison and contraction equality imply `Q = q D`:
   subtract from an element of `Q` a representative from `C`; its representative must
   lie in `q`. Extension of ideals commutes with powers, giving `Q^n = q^n D`.
5. Localize the canonical map at `q` and `Q`. It sends fractions `c/s` to `f(c)/f(s)`.
   By `def-weil-pbc-localization-at-prime` it is local. Apply
   `lem-weil-pbc-localization-at-prime-of-quotient` on both sides. The quotient
   equivalences of step 3 preserve the two prime complements and therefore localize
   to inverse ring maps. Their fraction formula is the displayed canonical formula.
6. For all positive `k ≥ n`, both composites in the transition square send the class
   of `c/s` to the class of `f(c)/f(s)`. Such classes exhaust the source, so the
   transition maps commute with these isomorphisms.
(blueprint: lem-trf-finite-type-base-change-adic-quotients) -/
theorem finiteTypeBaseChangeAdicQuotients
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {C : Type v} [CommRing C] [Algebra R C]
    (hC : RingHom.FiniteType (algebraMap R C))
    (q : Ideal C) [q.IsPrime]
    (hq : Ideal.map (algebraMap R C) (IsLocalRing.maximalIdeal R) ≤ q)
    (Q : Ideal (TensorProduct R C (AdicCompletion (IsLocalRing.maximalIdeal R) R)))
    [Q.IsPrime]
    (hQC : Ideal.comap
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := C)
        (B := AdicCompletion (IsLocalRing.maximalIdeal R) R)).toRingHom Q = q)
    (hQR : Ideal.comap
      (Algebra.TensorProduct.includeRight (R := R) (A := C)
        (B := AdicCompletion (IsLocalRing.maximalIdeal R) R)).toRingHom Q =
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
    ∃ e : ∀ n : ℕ,
      (Localization.AtPrime q ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ (n + 1)) ≃+*
      (Localization.AtPrime Q ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ (n + 1)),
      (∀ (n : ℕ) (x : Localization.AtPrime q),
        e n (Ideal.Quotient.mk _ x) =
          Ideal.Quotient.mk _
            (Localization.localRingHom q Q
              (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := C)
                (B := AdicCompletion (IsLocalRing.maximalIdeal R) R)).toRingHom hQC.symm x)) ∧
      ∀ (n k : ℕ) (hnk : n ≤ k),
        (Ideal.Quotient.factor (R := Localization.AtPrime Q)
          (Ideal.pow_le_pow_right (Nat.add_le_add_right hnk 1))).comp (e k).toRingHom =
        (e n).toRingHom.comp
          (Ideal.Quotient.factor (R := Localization.AtPrime q)
            (Ideal.pow_le_pow_right (Nat.add_le_add_right hnk 1))) := by
  sorry

end RingTheory
