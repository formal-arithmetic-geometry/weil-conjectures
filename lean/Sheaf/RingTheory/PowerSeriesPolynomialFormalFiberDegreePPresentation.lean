/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.Basic

import Sheaf.RingTheory.FiniteSubalgebraFractionField
import Sheaf.RingTheory.CompletionFiniteExtension
import Sheaf.RingTheory.CompletionFiniteQuotient
import Sheaf.RingTheory.Derivation.CompletionAndLocalization
import Sheaf.RingTheory.Derivation.DetectNonPthPower
import Sheaf.RingTheory.PurelyInseparableIntegralPrimeUnique
import Sheaf.RingTheory.RadicialPrimeUniqueDegreeP
import Sheaf.RingTheory.RegularRingNormal
import Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete
import Sheaf.RingTheory.RegularLocalLocalization

/-!
# Degree-p presentations of extended generic formal fibres

Source: Stacks Project, More on Algebra, Tag 07PR, finite-model and derivation paragraphs.
(blueprint: lem-weil-pbc-power-series-polynomial-degree-p-presentation)
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- A degree-p final step in a purely inseparable extension presents the extended formal
fibre as a binomial hypersurface over the preceding fibre. A derivation of that fibre
sends its constant coefficient to a unit.
Source: Stacks Project, More on Algebra, Tag 07PR, proof, finite-model and derivation
paragraphs; Tags 07N9, 07PH and 07PE.
(blueprint: lem-weil-pbc-power-series-polynomial-degree-p-presentation)

Proof:
Write A = k[[x]][y], K = Frac(A), and F = K tensor_A completion(A_q).
Choose a finite A-subalgebra B of M with fraction field M. Since A is regular, it is
normal, and the finite purely inseparable extension gives a unique prime r above q.
Write z^p = f in M and clear denominators: if f = b/s, replace z by sz and f by
s^(p-1)b in B. This keeps M(z) = L, degree p, and failure to be a pth power in M.
The monic quotient E = B[Z]/(Z^p-f) is finite free over B. Its map to L is injective
because the minimal polynomial of z over M has degree p; its fraction field is L.
Every pth power in E lies in B. Thus E has a unique prime t over r, and localizing
E at B minus r is already the local ring E_t: any prime contracts inside r, and the
pth-power condition puts that prime inside t. The completion of E_t is
completion(B_r)[Z]/(Z^p-f), by the finite-quotient completion theorem.
Apply the finite-extension completion decomposition to A -> B and A -> E. Each
product has one factor, by uniqueness of the primes over q. Tensor the first with M,
and the second with L. Tensor associativity, quotient base change and exchange of
factors identify M tensor_K F with R = completion(B_r) tensor_B M, and L tensor_K F
with R[Z]/(Z^p-f).
The domain B is finite type over the complete Noetherian power-series local ring.
Tag 07PH gives an absolute derivation D of B nonzero on f, since f is not a pth power
in M. Extend D through B_r, its completion, and its localization R using Tag 07PE.
Its value on f is the image of the nonzero field element D(f) in M, hence a unit
of R. Transport f and D to M tensor_K F using the first equivalence, and transport
the binomial quotient presentation along the induced coefficient isomorphism. These
are the required witnesses. No regularity of the preceding fibre is used in this
construction. Extending D coefficientwise and applying the regularity criterion are
left to the consumer of this presentation.

Edge cases: n or m may be zero. A zero formal fibre causes no exception: its
polynomial quotient and the extended fibre are zero rings, where zero is a unit.
Degree p is nontrivial because p is prime, so the non-pth-power argument applies. -/
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
  sorry

end MvPowerSeries
