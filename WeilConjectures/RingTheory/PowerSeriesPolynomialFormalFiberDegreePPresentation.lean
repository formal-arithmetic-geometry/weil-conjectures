/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.Basic

import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.Algebra.MonoidAlgebra.Defs

import WeilConjectures.RingTheory.FormalFiberDegreePDerivation
import WeilConjectures.RingTheory.FormalFiberDegreePQuotient

/-!
# Degree-p presentations of extended generic formal fibres

For a degree-`p` final step `L = M(z)` of a purely inseparable extension, the extended generic
formal fibre is a binomial hypersurface over the preceding fibre, which carries a derivation
sending the constant coefficient to a unit.

## Implementation details

No regularity of the preceding fibre is assumed or concluded. The statement also covers
zero formal fibres, where zero is a unit.

## References

* [Stacks Project, Tag 07PR](https://stacks.math.columbia.edu/tag/07PR), proof
* Stacks Project, Tags 07N9, 07PH and 07PE
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- A degree-p final step in a purely inseparable extension presents the extended formal
fibre as a binomial hypersurface over the preceding fibre. A derivation of that fibre
sends its constant coefficient to a unit. -/
theorem formalFiber_polynomial_degreePPresentation
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
    (hpow : ∃ f : M, z ^ p = (f : L)) (hdeg : Module.finrank M L = p) :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let K := (⊥ : Ideal A).ResidueField
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let R := TensorProduct K M ((⊥ : Ideal A).Fiber C)
    let T := TensorProduct K L ((⊥ : Ideal A).Fiber C)
    letI : CommSemiring R := (inferInstance : CommRing R).toCommSemiring
    letI : AddCommMonoid R := (inferInstance : CommRing R).toAddCommGroup.toAddCommMonoid
    letI : CommSemiring T := (inferInstance : CommRing T).toCommSemiring
    letI : AddCommMonoid T := (inferInstance : CommRing T).toAddCommGroup.toAddCommMonoid
    ∃ (f : R) (D : Derivation ℤ R R), IsUnit (D f) ∧
      Nonempty ((Polynomial R ⧸
        Ideal.span ({Polynomial.X ^ p - Polynomial.C f} : Set (Polynomial R))) ≃+* T) := by
  intro A K C R T
  -- Direct elimination avoids rechecking the entire dependent tensor-product goal at each step.
  refine hpow.elim fun a ha ↦ ?_
  refine (exists_derivation_isUnit_tmul_formalFiber k p n m q L M z hz a ha hdeg).elim
    fun D hD ↦ ?_
  have hiso := nonempty_quotient_X_pow_sub_C_ringEquiv_tensorProduct K L M ((⊥ : Ideal A).Fiber C)
    p z hz a ha hdeg
  exact ⟨Algebra.TensorProduct.includeLeftRingHom a, D, hD, hiso⟩

end MvPowerSeries
