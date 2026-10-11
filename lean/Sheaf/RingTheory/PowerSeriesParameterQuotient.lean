/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Sheaf.RingTheory.CohenRing
public import Sheaf.RingTheory.IsRegularSystemOfParameters

/-!
# Quotients of power series rings by partial parameter systems

Source: Stacks Project, More on Algebra, Lemma Tag 07NM, clauses (2) and (4)
(blueprint: lem-weil-pbc-power-series-parameter-quotient).
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- Quotienting field power series by the first part of a chosen regular parameter system
leaves power series with the remaining parameters as variables.
Source: Stacks Project, Lemma Tag 07NM (2)
(blueprint: lem-weil-pbc-power-series-parameter-quotient).

Proof: Extend the partial system to the displayed full system. Its linear part is invertible
on the cotangent space. Substitution therefore induces isomorphisms on every quotient by a
power of the maximal ideal, degree by degree; completeness makes substitution an isomorphism
(lem-weil-pbc-power-series-field-cohen-regular-complete). In these coordinates quotienting by
z sets the first variables to zero, leaving precisely the variables y
(def-weil-pbc-multivariate-power-series). Dimension gives the parameter count. The resulting
algebra equivalence is local. This is steps 1 and 2 of the node's proof. -/
theorem exists_algEquiv_quotient_parameters_field
    (K : Type u) [Field K] (n : ℕ)
    (z y : List (MvPowerSeries (Fin n) K))
    (hparams : IsLocalRing.IsRegularSystemOfParameters (z ++ y)) :
    z.length ≤ n ∧ y.length = n - z.length ∧
      ∃ e : MvPowerSeries (Fin y.length) K ≃ₐ[K]
          (MvPowerSeries (Fin n) K ⧸ Ideal.span {a | a ∈ z}),
        IsLocalHom e.toRingHom ∧
          ∀ i : Fin y.length, e (X i) = Ideal.Quotient.mk _ (y.get i) := by
  sorry

/-- In the Cohen case the coefficient uniformizer is retained, while quotienting by z
leaves power series in the remaining chosen parameters over the same Cohen ring.
Source: Stacks Project, Lemma Tag 07NM (4)
(blueprint: lem-weil-pbc-power-series-parameter-quotient).

Proof: The full system consists of p, then z, then y. Substitution fixes the coefficient ring
and p. Its invertible cotangent map induces isomorphisms modulo every maximal-ideal power;
completeness gives an algebra isomorphism
(lem-weil-pbc-power-series-field-cohen-regular-complete and def-weil-pbc-cohen-ring).
Quotienting in these coordinates kills just z, leaving power series in y
(def-weil-pbc-multivariate-power-series). Dimension counts the surviving variables. The
algebra equivalence fixes the coefficient uniformizer and is local. These are steps 3 and 4
of the node's proof. -/
theorem exists_algEquiv_quotient_parameters_cohen
    (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    (p n : ℕ) (hΛ : IsCohenRing p Λ)
    (z y : List (MvPowerSeries (Fin n) Λ))
    (hparams : IsLocalRing.IsRegularSystemOfParameters (C (p : Λ) :: (z ++ y))) :
    z.length ≤ n ∧ y.length = n - z.length ∧
      ∃ e : MvPowerSeries (Fin y.length) Λ ≃ₐ[Λ]
          (MvPowerSeries (Fin n) Λ ⧸ Ideal.span {a | a ∈ z}),
        IsLocalHom e.toRingHom ∧
          (∀ i : Fin y.length, e (X i) = Ideal.Quotient.mk _ (y.get i)) ∧
          e (C (p : Λ)) = Ideal.Quotient.mk _ (C (p : Λ)) := by
  sorry

end MvPowerSeries
