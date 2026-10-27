/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.RingTheory.CompleteToricModel
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Residue units and prime coordinates of supported complete toric covers

Source: ILO, Travaux de Gabber, Exposé VI 1.4 and 1.6(i)--(ii), printed pp. 69--70,
for the complete local models only. The residue and prime-coordinate assertions are
agent-formulated auxiliary algebra (blueprint: lem-trf-supported-coordinate-cover-units-primes).

The first and second variable blocks are `Fin r` and `Fin n`. Surjective maps with
specified kernels present the identity maps in the field case and the canonical
principal quotients in the Cohen case, allowing any isomorphic realization of them.
-/

@[expose] public section

universe u v w x

namespace ToricMonoid

open Classical in
/-- The supported complete cover has the stated common residue field and unit criterion;
coefficient deletion preserves residue and units; the ambient ring is a Noetherian
normal domain and its first-block coordinates generate distinct height-one primes.

Source: complete model presentations in ILO VI 1.6(i)--(ii), printed p. 70;
agent auxiliary statement (blueprint: lem-trf-supported-coordinate-cover-units-primes).

Proof: (1) Injectivity of the lattice map makes every nonzero chart monomial
nonconstant. Thus in the Cohen case the constant coefficient of the defining series
is exactly p. Apply lem-trf-power-series-cohen-hypersurface-normality to obtain a
Noetherian normal domain D. Use lem-weil-pbc-power-series-quotient-variables for the
constant coefficient map, and lem-weil-pbc-power-series-local-ring for locality of A.
(2) For a supported series with invertible constant c, put h = c⁻¹b - 1. The inverse
c⁻¹ sum (-h)^j exists coefficientwise, since only j up to the total degree contributes.
Its support stays in the additive support monoid. This proves the residue unit
criterion and locality for B. (3) In the Cohen case theta and its image have zero
residue, so the residue maps descend to R and D. A class with nonzero residue lifts
to a unit, whose inverse descends. This proves locality and the unit criteria in both
quotients. (4) Coefficient deletion fixes the constant coefficient, so the induced
retraction preserves residue and therefore sends units to units.
(5) Set one coordinate to zero using lem-weil-pbc-power-series-quotient-variables.
The quotient is the series ring on the remaining variables, or its Cohen hypersurface
quotient, still with constant coefficient p. The normality lemma makes this a domain,
so each coordinate ideal is prime. (6) A variable is nonzero in a field series ring.
If a variable Y were F*a in a Cohen quotient, constants give p*a₀ = 0, so a₀ = 0;
the coefficient of Y then gives 1 = p*a_Y, impossible. Apply this also after setting
another variable to zero, proving distinctness of the coordinate ideals.
(7) Apply lem-sfb-krull-principal-ideal-height-bound to each principal prime ideal;
nonzero coordinates give the strict lower bound. This yields height one in the
stated no-intermediate-prime sense. Empty variable blocks require no exception. -/
theorem supportedCoordinateCover_units_primes
    (P : Type u) [AddCommMonoid P]
    (hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P))
    (hsharp : ∀ a b : P, a + b = 0 → a = 0 ∧ b = 0)
    (r n : ℕ) (lam : Lattice P →+ (Fin r → ℤ)) (hlam : Function.Injective lam)
    (horthant : ∀ v : Fin r → ℤ,
      (v ∈ lam.range ∧ ∀ i : Fin r, 0 ≤ v i) ↔ ∃ q : P, lam (latticePoint q) = v)
    (L : Type v) [CommRing L] [IsLocalRing L]
    (ι : Complete L P n →ₐ[L] MvPowerSeries (Fin r ⊕ Fin n) L)
    (hι : Function.Injective ι)
    (hsupport : ∀ f : MvPowerSeries (Fin r ⊕ Fin n) L,
      (∃ b : Complete L P n, ι b = f) ↔
        ∀ e : (Fin r ⊕ Fin n) →₀ ℕ,
          (fun i : Fin r ↦ (e (Sum.inl i) : ℤ)) ∉ lam.range →
            MvPowerSeries.coeff e f = 0)
    (hmonomial : ∀ (q : P) (e : (Fin r ⊕ Fin n) →₀ ℕ),
      MvPowerSeries.coeff e (ι (monomial L P n q)) =
        if (∀ i : Fin r, (e (Sum.inl i) : ℤ) = lam (latticePoint q) i) ∧
            (∀ j : Fin n, e (Sum.inr j) = 0) then 1 else 0)
    (hvariable : ∀ j : Fin n,
      ι (algebraMap (PolynomialRing L P n) (Complete L P n) (MvPolynomial.X j)) =
        MvPowerSeries.X (Sum.inr j))
    (ρ : MvPowerSeries (Fin r ⊕ Fin n) L →+ Complete L P n)
    (hρ : ∀ (f : MvPowerSeries (Fin r ⊕ Fin n) L) (e : (Fin r ⊕ Fin n) →₀ ℕ),
      MvPowerSeries.coeff e (ι (ρ f)) =
        if (fun i : Fin r ↦ (e (Sum.inl i) : ℤ)) ∈ lam.range then
          MvPowerSeries.coeff e f else 0)
    (R : Type w) [CommRing R] (D : Type x) [CommRing D]
    (qB : Complete L P n →+* R) (qA : MvPowerSeries (Fin r ⊕ Fin n) L →+* D)
    (hqB : Function.Surjective qB) (hqA : Function.Surjective qA)
    (hcase :
      (IsField L ∧ RingHom.ker qB = ⊥ ∧ RingHom.ker qA = ⊥) ∨
      (∃ (p : ℕ) (θ : Complete L P n), IsCohenRing p L ∧
        θ - (p : Complete L P n) ∈ completedChartIdeal L P n ∧
        RingHom.ker qB = Ideal.span {θ} ∧ RingHom.ker qA = Ideal.span {ι θ}))
    (j : R →+* D) (hj : Function.Injective j)
    (hcommute : ∀ b : Complete L P n, j (qB b) = qA (ι b))
    (ρbar : D →+ R)
    (hdescend : ∀ f : MvPowerSeries (Fin r ⊕ Fin n) L, ρbar (qA f) = qB (ρ f))
    (hretract : ∀ a : R, ρbar (j a) = a)
    (hlinear : ∀ (a : R) (b : D), ρbar (j a * b) = a * ρbar b) :
    ∃ (_ : IsLocalRing (Complete L P n)) (_ : IsLocalRing R) (_ : IsLocalRing D),
      ∃ (resB : Complete L P n →+* IsLocalRing.ResidueField L)
        (resR : R →+* IsLocalRing.ResidueField L)
        (resD : D →+* IsLocalRing.ResidueField L),
        (∀ b : Complete L P n,
          resB b = IsLocalRing.residue L (MvPowerSeries.constantCoeff (ι b))) ∧
        resR.comp qB = resB ∧
        (∀ f : MvPowerSeries (Fin r ⊕ Fin n) L,
          resD (qA f) = IsLocalRing.residue L (MvPowerSeries.constantCoeff f)) ∧
        Function.Surjective resB ∧ Function.Surjective resR ∧ Function.Surjective resD ∧
        RingHom.ker resB = IsLocalRing.maximalIdeal (Complete L P n) ∧
        RingHom.ker resR = IsLocalRing.maximalIdeal R ∧
        RingHom.ker resD = IsLocalRing.maximalIdeal D ∧
        (∀ b : Complete L P n, IsUnit b ↔ resB b ≠ 0) ∧
        (∀ a : R, IsUnit a ↔ resR a ≠ 0) ∧ (∀ b : D, IsUnit b ↔ resD b ≠ 0) ∧
        (∀ b : D, resR (ρbar b) = resD b) ∧
        (∀ b : D, IsUnit b → IsUnit (ρbar b)) ∧
        IsNoetherianRing D ∧ IsDomain D ∧ IsIntegrallyClosed D ∧
        (∀ i : Fin r, Prime (qA (MvPowerSeries.X (Sum.inl i))) ∧
          (Ideal.span {qA (MvPowerSeries.X (Sum.inl i))}).IsPrime ∧
          Ideal.span {qA (MvPowerSeries.X (Sum.inl i))} ≠ ⊥ ∧
          ∀ I : Ideal D, I.IsPrime → I ≤ Ideal.span {qA (MvPowerSeries.X (Sum.inl i))} →
            I = ⊥ ∨ I = Ideal.span {qA (MvPowerSeries.X (Sum.inl i))}) ∧
        Function.Injective (fun i : Fin r ↦
          Ideal.span {qA (MvPowerSeries.X (Sum.inl i))}) := by
  sorry

end ToricMonoid
