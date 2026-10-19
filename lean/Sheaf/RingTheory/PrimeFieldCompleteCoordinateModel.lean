/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Sheaf.AlgebraicGeometry.IsRegularScheme

import WeilConjectures.RingTheory.ExistsCoefficientSubring
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Complete regular local rings over prime fields

Source: Stacks Project, Algebra, Tag 0C0S, `lemma-regular-complete-containing-coefficient-field`
(blueprint: lem-per-prime-field-complete-coordinate-model).
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace IsLocalRing

/-- A complete equicharacteristic regular local ring has coefficient-field coordinates.

Source: Stacks Project, Algebra, Tag 0C0S, `lemma-regular-complete-containing-coefficient-field`,
clauses (1) and (2), together with the coefficientwise description of the adic completion
of the polynomial ring (blueprint: lem-per-prime-field-complete-coordinate-model).

Proof (the node's six steps):
1. Apply `lem-weil-pbc-cohen-coefficient-ring-exists`. In characteristic zero the residue
   characteristic is zero; in characteristic p, p vanishes in B and in the coefficient
   subring. Its maximal ideal is therefore zero. Its residue isomorphism gives σ.
2. Noetherianity and `lem-weil-pbc-noetherian-local-dimension-le-generators` make the
   dimension finite. Regularity supplies d generators t of the maximal ideal.
3. Use `lem-weil-pbc-power-series-field-cohen-regular-complete` over F = B/m and
   `lem-weil-pbc-power-series-universal-property-complete` with σ and t. The resulting
   map Φ is surjective by `lem-weil-pbc-complete-source-surjective-mod-ideal`, since
   constants already surject onto F and the variables generate m.
4. A nonzero element of ker Φ, together with the inverse image of a prime chain of
   length d in B, would give a prime chain of length d+1 in the power-series domain.
   This contradicts its dimension d. Thus Φ gives e. Powers of the variables' ideal
   map into the corresponding powers of m, proving adic continuity.
5. For C = F[T] and I = (T), classes modulo I^n have unique representatives of degree
   less than n. Stable coefficients give the canonical equivalence of its completion
   with F[[T]]. Compose this equivalence with e to obtain ec. Its restriction to C is
   polynomial evaluation at t with coefficient map σ, so it is the induced map.
6. Modulo I this equivalence is the constant coefficient map, and residue ∘ σ is the
   identity. Hence ec induces the identity on C/I = F = B/m. For d = 0 the empty
   parameter family generates m = 0, and the polynomial and series rings both reduce
   to F; all the displayed maps include this case without a positivity hypothesis.
-/
theorem exists_prime_field_complete_coordinate_model
    (B : Type u) [CommRing B] [IsRegularLocalRing B]
    [IsAdicComplete (maximalIdeal B) B]
    (hchar : (∃ p : ℕ, Nat.Prime p ∧ CharP B p) ∨
      ∃ ι : ℚ →+* B, Function.Injective ι) :
    ∃ (d : ℕ), ringKrullDim B = (d : WithBot ℕ∞) ∧
      ∃ (σ : ResidueField B →+* B),
        (residue B).comp σ = RingHom.id (ResidueField B) ∧
        ∃ (t : Fin d → B),
          (∀ i : Fin d, t i ∈ maximalIdeal B) ∧
          Ideal.span (Set.range t) = maximalIdeal B ∧
          ∃ e : MvPowerSeries (Fin d) (ResidueField B) ≃+* B,
            (∀ a : ResidueField B, e (MvPowerSeries.C a) = σ a) ∧
            (∀ i : Fin d, e (MvPowerSeries.X i) = t i) ∧
            @Continuous _ _
              (Ideal.span (Set.range
                (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ResidueField B)))).adicTopology
              (maximalIdeal B).adicTopology e ∧
            ∃ ec : AdicCompletion (MvPolynomial.idealOfVars (Fin d) (ResidueField B))
                (MvPolynomial (Fin d) (ResidueField B)) ≃+* B,
              ec = (MvPowerSeries.toAdicCompletionAlgEquiv
                (Fin d) (ResidueField B)).toRingEquiv.symm.trans e ∧
              (∀ c : MvPolynomial (Fin d) (ResidueField B),
                ec (AdicCompletion.of (MvPolynomial.idealOfVars (Fin d) (ResidueField B))
                  (MvPolynomial (Fin d) (ResidueField B)) c) = MvPolynomial.eval₂ σ t c) ∧
              (∀ (z : AdicCompletion (MvPolynomial.idealOfVars (Fin d) (ResidueField B))
                    (MvPolynomial (Fin d) (ResidueField B)))
                  (c : MvPolynomial (Fin d) (ResidueField B)),
                AdicCompletion.evalOneₐ (MvPolynomial.idealOfVars (Fin d) (ResidueField B)) z =
                  Ideal.Quotient.mk _ c →
                residue B (ec z) = MvPolynomial.constantCoeff c) := by
  sorry

end IsLocalRing
