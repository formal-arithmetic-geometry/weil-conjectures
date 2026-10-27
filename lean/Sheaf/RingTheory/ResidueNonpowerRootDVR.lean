module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Adjoining a radical with nonpower residue

Source: Stacks Project, Tag 09EX, `lemma-pre-purely-inseparable-case`, with the
residue-field presentation from the monic root algebra
(blueprint: lem-sfb-epp-residue-nonpower-root-dvr).
-/

@[expose] public section

universe u v w

namespace IsDiscreteValuationRing

/-- Adjoining a `p`th root whose residue is not a `p`th power gives a DVR with the
same uniformizer and the indicated residue field, and already gives the integral closure.
Source: Stacks Project, Tag 09EX, `lemma-pre-purely-inseparable-case`
(blueprint: lem-sfb-epp-residue-nonpower-root-dvr).

Proof plan:
1. Form `C = R[T]/(T^p-a)`. The monic power basis makes it finite free; reduction
   modulo `t` is `k[T]/(T^p-a_bar)` (lem-weil-pbc-monic-quotient-free). The latter is
   a field by lem-weil-pbc-x-pow-p-minus-t-irreducible and
   lem-trf-irreducible-polynomial-quotient-field, so `tC` is maximal.
2. The algebra `C` is integral over `R` (lem-weil-pbc-finite-algebra-is-integral).
   Every maximal ideal contracts to the maximal ideal of `R`
   (lem-weil-pbc-integral-maximal-contracts-maximal), hence equals `tC`.
3. Factor each nonzero coefficient as a unit times a power of `t`
   (lem-weil-pbc-dvr-unit-times-uniformizer-power). Extract the smallest power.
   The remaining element has nonzero residue and is a unit
   (lem-weil-pbc-local-ring-unit-criterion).
4. Evaluation at `z` is injective by this factorization, identifying `C` with `R[z]`.
   Clearing denominators identifies its fraction field with `F(z)`; its power basis
   then gives degree `p` over `F`.
5. The least exponent of a nonzero element of any nonzero ideal generates that ideal.
   Thus `C` is a local principal ideal domain, not a field, with uniformizer `t`
   (def-sc-discrete-valuation-ring). Reduction of the power basis gives the displayed
   residue presentation, with the coefficient and root identifications stated below.
6. A PID is integrally closed (lem-weil-pbc-pid-noetherian-normal). Elements of `C`
   are integral over `R`, and any element of `F(z)` integral over `R` is integral over
   `C` and hence lies in `C` (def-weil-pbc-integral-closure).
No completeness or characteristic hypothesis on `F` is used. -/
theorem residue_nonpower_root_dvr
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
    (E : Type w) [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField R) p]
    (t : R) (ht : Irreducible t) (a : R)
    (ha : ∀ x : IsLocalRing.ResidueField R, x ^ p ≠ IsLocalRing.residue R a)
    (z : E) (hz : z ^ p = algebraMap R E a)
    (hE : IntermediateField.adjoin F ({z} : Set E) = ⊤) :
    Module.finrank F E = p ∧
      integralClosure R E = Algebra.adjoin R ({z} : Set E) ∧
      IsDiscreteValuationRing (Algebra.adjoin R ({z} : Set E)) ∧
      Irreducible (algebraMap R (Algebra.adjoin R ({z} : Set E)) t) ∧
      ∃ e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C (IsLocalRing.residue R a)) ≃+*
          (Algebra.adjoin R ({z} : Set E) ⧸
            Ideal.span {algebraMap R (Algebra.adjoin R ({z} : Set E)) t}),
        (∀ r : R,
          e (AdjoinRoot.of
            (Polynomial.X ^ p - Polynomial.C (IsLocalRing.residue R a))
            (IsLocalRing.residue R r)) =
          Ideal.Quotient.mk _ (algebraMap R (Algebra.adjoin R ({z} : Set E)) r)) ∧
        e (AdjoinRoot.root
          (Polynomial.X ^ p - Polynomial.C (IsLocalRing.residue R a))) =
          Ideal.Quotient.mk _ ⟨z, Algebra.self_mem_adjoin_singleton R z⟩ := by
  sorry

end IsDiscreteValuationRing
