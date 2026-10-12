/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic

import Sheaf.RingTheory.FiniteSubalgebraFractionField
import Sheaf.RingTheory.CompletionFiniteExtension
import Sheaf.RingTheory.Derivation.CompletionAndLocalization
import Sheaf.RingTheory.Derivation.DetectNonPthPower
import Sheaf.RingTheory.PurelyInseparableIntegralPrimeUnique
import Sheaf.RingTheory.RegularRingNormal
import Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete
import Sheaf.RingTheory.RegularLocalLocalization
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Degree-p formal-fibre derivation component

Source: Stacks Project, More on Algebra, Tag 07PR.
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- A derivation detects the specified degree-p coefficient in the extended formal fibre.
Source: Stacks Project, More on Algebra, Tags 07PR, 07PH and 07PE.
(blueprint: new-lem-weil-pbc-degree-p-derivation-component)

Proof: The element a is not a pth power in M. Otherwise injectivity of Frobenius
in L implies z belongs to M, contradicting [L:M] = p > 1. Choose a finite
A-subalgebra B with fraction field M. Write a = b/s, with s nonzero in B,
and set c = s^(p-1)b, so c = s^p a in M and c is not a pth power in M.
The power-series base is Noetherian complete local and B is finite type over it.
Tag 07PH supplies an absolute derivation of B nonzero on c. Normality of A and
pure inseparability give a unique prime r over q. Finite-extension completion
and tensor associativity identify R with completion(B_r) tensor_B M.
Extend the derivation through B_r, its completion, and this localization by
Tag 07PE. Its value on c is the image of a nonzero element of M, hence is a unit.
Characteristic p implies D(s^p) = 0. Thus D(i(a)) = i(s)^(-p) D(i(c)),
which is a unit. Transport the derivation along the ring equivalence with R.
If R is zero, zero is a unit, and the same identities still apply. -/
theorem FormalFiberDegreePDerivation
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime]
    (L : Type u) [Field L]
    [Algebra ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    [Module.Finite
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    [IsPurelyInseparable
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    (M : IntermediateField
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L)
    [Module.Finite
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    [IsPurelyInseparable
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    (z : L) (hz : IntermediateField.adjoin M ({z} : Set L) = ⊤)
    (a : M) (ha : z ^ p = (a : L)) (hdeg : Module.finrank M L = p) :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let K := (⊥ : Ideal A).ResidueField
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let R := TensorProduct K M ((⊥ : Ideal A).Fiber C)
    letI : CommSemiring R := (inferInstance : CommRing R).toCommSemiring
    letI : AddCommMonoid R := (inferInstance : CommRing R).toAddCommGroup.toAddCommMonoid
    ∃ D : Derivation ℤ R R, IsUnit (D (Algebra.TensorProduct.includeLeftRingHom a)) := by
  sorry

end MvPowerSeries
