/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.FieldTheory.PurelyInseparableDegreePIntermediate
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.HypersurfaceDerivationRegular
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.PowerSeriesPolynomialFormalFiberDegreePPresentation
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Geometric regularity of the characteristic-p formal fibre

In positive characteristic, the generic formal fibre of a polynomial ring over a finite variable
power series field stays regular after every finite purely inseparable base change.

## Implementation details

The base-change tensor product is the source's `Â ⊗_A L`, up to associativity and exchange of
factors. Only the regularity condition is supplied here; Noetherianity of the original fibre is
established independently.

## References

* [Stacks, Tag 07PR]
* [Stacks, Tag 07PG]
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- The generic formal fibre is regular, as a localization of a regular completion. -/
private theorem generic_fiber_regular
    (k : Type u) [Field k] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime] :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    IsRegularRing ((⊥ : Ideal A).Fiber C) := by
  let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
  let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (Localization.AtPrime q)
  have hps := power_series_field_cohen_regular_complete (Λ := k) n
    (Or.inl (Field.toIsField k))
  have hreg : IsRegularLocalRing (MvPowerSeries (Fin n) k) := by
    rcases hps with ⟨_, _, _, _, _, e, _, _, hr, _⟩ | ⟨p, hp, _⟩
    · exact hr
    · rcases hp with ⟨_, hd, hv, _⟩
      let := hd
      let := hv
      exact False.elim (IsDiscreteValuationRing.not_isField k (Field.toIsField k))
  let := hreg
  have : IsRegularRing (MvPowerSeries (Fin n) k) :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) k))).2
  have : IsRegularRing A := inferInstance
  have : IsRegularLocalRing C := (AdicCompletion.isRegularLocalRing_iff _).mp inferInstance
  have : IsRegularRing C :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal C)).2
  let T := Algebra.algebraMapSubmonoid C (⊥ : Ideal A).primeCompl
  have : IsRegularRing (Localization T) := inferInstance
  let : Algebra C ((⊥ : Ideal A).Fiber C) := Algebra.TensorProduct.rightAlgebra
  let e := (Ideal.Fiber.algEquivAux₁ (S := C) (⊥ : Ideal A)).toRingEquiv
  have : IsRegularRing
      (Localization T ⧸ ((⊥ : Ideal A).map (algebraMap A C)).map
        (algebraMap C (Localization T))) := by
    rw [Ideal.map_bot, Ideal.map_bot]
    exact IsRegularRing.of_ringEquiv (RingEquiv.quotientBot (Localization T)).symm
  exact IsRegularRing.of_ringEquiv e.symm

/-- A binomial quotient `R[z]/(z^p - f)` is regular if `R` is and a derivation of `R` sends `f`
to a unit. -/
private theorem regular_binomial_quotient
    (R : Type u) [CommRing R] [IsRegularRing R]
    (f : R) (D : Derivation ℤ R R) (hD : IsUnit (D f)) (p : ℕ) :
    IsRegularRing (Polynomial R ⧸
      Ideal.span ({Polynomial.X ^ p - Polynomial.C f} : Set (Polynomial R))) := by
  let E : Derivation ℤ (Polynomial R) (Polynomial R) :=
    PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs
  have hX : E Polynomial.X = 0 := by
    simp [E]
  have hC : E (Polynomial.C f) = Polynomial.C (D f) := by
    simp [E]
  have hEq : E (Polynomial.X ^ p - Polynomial.C f) = -Polynomial.C (D f) := by
    rw [map_sub, E.leibniz_pow, hX, smul_zero, smul_zero, hC, zero_sub]
  have hunit : IsUnit (Ideal.Quotient.mk
      (Ideal.span ({Polynomial.X ^ p - Polynomial.C f} : Set (Polynomial R)))
      (E (Polynomial.X ^ p - Polynomial.C f))) := by
    rw [hEq]
    exact ((hD.map Polynomial.C).neg).map _
  exact IsRegularRing.quotient_span_singleton_of_isUnit_derivation
    (Polynomial R) _ E hunit

/-- Regularity of the generic formal fibre after each finite purely inseparable base change. -/
theorem formalFiber_polynomial_geometricComponent
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime] :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    ∀ (k' : Type u) [Field k'] [Algebra ((⊥ : Ideal A).ResidueField) k']
      [Module.Finite ((⊥ : Ideal A).ResidueField) k']
      [IsPurelyInseparable ((⊥ : Ideal A).ResidueField) k'],
      IsRegularRing (TensorProduct ((⊥ : Ideal A).ResidueField) k'
        ((⊥ : Ideal A).Fiber C)) := by
  set_option backward.isDefEq.respectTransparency false in
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let K := (⊥ : Ideal A).ResidueField
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let F := (⊥ : Ideal A).Fiber C
    have : IsDomain A := NoZeroDivisors.to_isDomain A
    have : CharP (MvPowerSeries (Fin n) k) p :=
      charP_of_injective_ringHom (MvPowerSeries.C_injective (σ := Fin n)) p
    have : CharP A p := charP_of_injective_ringHom (MvPolynomial.C_injective (Fin m) _) p
    have : CharP K p := IsFractionRing.charP_of_isFractionRing A p
    have hbase : IsRegularRing F := generic_fiber_regular k n m q
    have hdegree (d : ℕ) :
        ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
          [IsPurelyInseparable K L], Module.finrank K L = d →
          IsRegularRing (TensorProduct K L F) := by
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro L _ _ _ _ hd
        by_cases h1 : Module.finrank K L = 1
        · obtain ⟨e⟩ := Module.nonempty_algEquiv_iff_finrank_eq_one.mpr h1
          let eF := (Algebra.TensorProduct.congr e (AlgEquiv.refl : F ≃ₐ[K] F)).symm.trans
            (Algebra.TensorProduct.lid K F)
          exact IsRegularRing.of_ringEquiv eF.symm.toRingEquiv
        · have hgt : 1 < Module.finrank K L :=
            lt_of_le_of_ne Module.finrank_pos (Ne.symm h1)
          obtain ⟨M, z, hfin, hpure, hlt, hz, hpow, hdeg⟩ :=
            IsPurelyInseparable.exists_degree_p_intermediate K L p
              (Fact.out : p.Prime).pos hgt
          let := hfin
          let := hpure
          have hM : IsRegularRing (TensorProduct K M F) :=
            ih (Module.finrank K M) (hd ▸ hlt) M rfl
          let := hM
          obtain ⟨f, D, hunit, ⟨e⟩⟩ :=
            formalFiber_polynomial_degreePPresentation k p n m q L M z hz hpow hdeg
          have := regular_binomial_quotient (TensorProduct K M F) f D hunit p
          exact IsRegularRing.of_ringEquiv
            (R := Polynomial (TensorProduct K M F) ⧸
              Ideal.span ({Polynomial.X ^ p - Polynomial.C f} : Set _)) e
    change ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
      [IsPurelyInseparable K L], IsRegularRing (TensorProduct K L F)
    intro L _ _ _ _
    exact hdegree (Module.finrank K L) L rfl

end MvPowerSeries
