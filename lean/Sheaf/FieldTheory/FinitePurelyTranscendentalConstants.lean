/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Sheaf.FieldTheory.PurelyTranscendentalExtension
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Constants in a finite purely transcendental field extension

Source: Stacks Project, More on Morphisms, Tag 057K, proof paragraph beginning
"Let T be the connected component"; the implicit field-theoretic input is expanded
in the DAG proof using Tag 030A and `MvPolynomial.dvd_C_iff_exists`.
(blueprint: lem-trf-pure-transcendental-relatively-algebraically-closed)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

private theorem finite_mvPolynomial_isIntegrallyClosed
    (k : Type u) [Field k] (r : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin r) k) := by
  induction r with
  | zero =>
    exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm
  | succ r ih =>
    let := ih
    exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv k r).symm.toRingEquiv

/-- An algebraic element of a field extension presented as a rational function field
in finitely many variables over the base field is a scalar. The indeterminates of
`MvPolynomial (Fin r) k` are algebraically independent, and `FractionRing` supplies
exactly the fraction-field presentation. This finite presentation is the finite-variable
case of `Algebra.IsPurelyTranscendentalExtension`, including `r = 0`.

Source: Stacks Project, More on Morphisms, Tag 057K, proof paragraph beginning
"Let T be the connected component" (implicit field-theoretic input).
(blueprint: lem-trf-pure-transcendental-relatively-algebraically-closed)

Proof:
1. Choose `r` and the given `k`-algebra equivalence to work in the fraction field
   `F` of `A = k[U_1, ..., U_r]`. The equivalence preserves polynomial relations
   and scalars. Algebraic independence identifies the polynomial presentation
   injectively. The case `r = 0` is the trivial extension; zero is already a scalar.
2. A field is a normal domain. Inductively apply
   `lem-weil-pbc-polynomial-ring-normal-domain` (Stacks 030A) to show that `A` is
   a normal domain. Grouping monomials by the exponent of the final variable
   identifies the successive one-variable polynomial rings with `A`.
3. For a nonzero algebraic element, factor the highest possible power of `T` out
   of a nonzero annihilating polynomial. The remaining polynomial still vanishes
   and has nonzero constant term. Divide by its leading coefficient to get a monic
   relation of positive degree with nonzero constant term. Regard its coefficients
   as elements of `A`. Integral closedness of `A` gives `h` in `A` representing
   the element in `F`.
4. Injectivity of `A` into `F` gives this monic relation already in `A`.
   Isolating its nonzero constant term shows that `h` divides that constant.
   Apply `lem-trf-mvpolynomial-divisor-nonzero-constant`, namely
   `MvPolynomial.dvd_C_iff_exists`, to conclude that `h` is constant. Transport
   this scalar back along the original `k`-algebra equivalence.
-/
theorem exists_algebraMap_eq_of_isAlgebraic_of_finite_purelyTranscendental
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (htrans : ∃ r : ℕ, Nonempty (L ≃ₐ[k] FractionRing (MvPolynomial (Fin r) k)))
    {α : L} (hα : IsAlgebraic k α) :
    ∃ a : k, algebraMap k L a = α := by
  obtain ⟨r, ⟨e⟩⟩ := htrans
  let A := MvPolynomial (Fin r) k
  let F := FractionRing A
  let : IsIntegrallyClosed A := finite_mvPolynomial_isIntegrallyClosed k r
  have hx : IsIntegral k (e α) := hα.isIntegral.map e.toAlgHom
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (hx.tower_top : IsIntegral A (e α))
  have hpint : IsIntegral k p := by
    apply (isIntegral_algebraMap_iff (IsFractionRing.injective A F)).mp
    rwa [hp]
  by_cases hp0 : p = 0
  · refine ⟨0, e.injective ?_⟩
    simpa only [hp0, map_zero] using hp
  · have hpdvd : p ∣ MvPolynomial.C (1 : k) := by
      simpa only [map_one] using (isUnit_iff_dvd_one.mp (hpint.isUnit hp0))
    obtain ⟨a, _, hpa⟩ := (MvPolynomial.dvd_C_iff_exists (one_ne_zero : (1 : k) ≠ 0)).mp
      hpdvd
    refine ⟨a, e.injective ?_⟩
    rw [e.commutes, ← hp, hpa]
    exact (IsScalarTower.algebraMap_apply k A F a).symm

end Algebra
