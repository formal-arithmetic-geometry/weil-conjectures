/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.CompleteLocalSubideal
import Sheaf.TraceFormula.HenselizationQuotientAtPrime
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Sheaf.RingTheory.PairHenselizationFlatQuotients
import Sheaf.RingTheory.PairHenselizationNoetherianCompletion
import Sheaf.RingTheory.PowerSeriesAdicEvaluation
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import Sheaf.RingTheory.PowerSeriesCompleteOverCompleteBase
import WeilConjectures.RingTheory.QuotientHenselianPair
import Sheaf.RingTheory.LocalPairHenselizationComparison
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Weierstrass coordinates and the henselian cylinder

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose V, Theorem 1.1.1,
Lemmas 1.1.3 and 1.2.3, and proof 2.2.3
(blueprint: lem-per-weierstrass-henselian-cylinder).

We write `r = s + 1` and regroup the last variable as the outer power-series variable.
Thus `MvPowerSeries.finSuccEquiv` identifies the ring in the statement with the ring here
(up to reindexing the distinguished variable). The case `s = 0` is included.
The prime `q` is the inverse image of the coefficient maximal ideal under evaluation at zero.
The map `a` below is explicitly the polynomial-to-henselization structure map; the local
map `φ` is characterized by extending the polynomial inclusion. The henselization universal
property therefore makes it canonical, rather than an arbitrary faithfully flat map.
-/

@[expose] public section
set_option autoImplicit false

universe u v

namespace RingTheory

/-- Weierstrass change of coordinates and both completions of the local henselian cylinder.
Source: Travaux de Gabber, Expose V, 1.1.1(i),(ii), 1.1.3, 1.2.3 and 2.2.3
(blueprint: lem-per-weierstrass-henselian-cylinder).

Proof (the ten steps of the node):
1. Regroup coefficients, using finite convolution for multiplicativity. Power-series
   Noetherianity, locality and completeness give these properties for D and R
   (lem-weil-pbc-power-series-noetherian, -local-ring, -complete-over-complete-base).
2. Reduce modulo the base maximal ideal. Choose the lexicographically first supported
   exponent a, then positive weights w_r=1 and w_i=1+sum_{j>i} a_j w_j. This exponent
   uniquely minimizes weight. The substitutions t_i -> t_i+T^{w_i} and their minus-sign
   inverses are continuous by lem-weil-pbc-power-series-adic-evaluation. Truncation and
   separatedness show they are inverse and fix the base power-series ring. The least
   coefficient of the specialization to the T-axis is nonzero. With no other variables
   use the identity.
3. Apply lem-per-weierstrass-preparation-complete-local. The resulting distinguished
   polynomial has positive degree because f is a nonunit.
4. Localize D[T] at q. It is Noetherian by the finite-type and localization lemmas.
   Use lem-per-local-pair-henselization-comparison and the pair-henselization Noetherian
   completion theorem to get the ordinary henselization's Noetherianity and residue field.
   The inclusion into R extends locally, since denominators outside q have unit constant
   coefficient. Completeness makes R henselian (lem-weil-pbc-complete-pair-henselian),
   so the ordinary henselization universal property supplies the canonical map.
5. Truncation gives D[T]/q^N = R/m_R^N: the coefficient criterion is
   lem-weil-pbc-power-series-combined-ideal-coefficients. Denominators outside q are
   invertible by a finite geometric sum. Apply lem-weil-pbc-henselization-flat-quotients
   and take inverse limits to identify the maximal-ideal completion with R.
6. Apply lem-weil-pbc-local-completion-faithfully-flat to this identification.
7. For each finite H-algebra, lem-weil-pbc-finite-over-henselian-local-product decomposes
   it into local factors. Since g lies in each maximal ideal, quotienting by g preserves
   the two idempotents 0 and 1 bijectively in each factor. Products, including the empty
   product, give the henselian-pair condition.
8. Each g^N is distinguished. By lem-per-distinguished-polynomial-quotient its polynomial
   quotient equals R/g^N. The latter is henselian local by
   lem-weil-pbc-quotient-henselian-pair. Localization outside q changes nothing.
9. Apply lem-trf-henselization-quotient-at-prime. The quotient of the localized polynomial
   ring is already henselian, so its henselization map is an isomorphism by uniqueness.
   Thus H/g^N -> R/g^N is the canonical isomorphism, compatibly for every N.
10. By lem-sbc-complete-local-subideal, R is g-adically complete. Taking inverse limits
    in step 9 gives the g-adic completion equivalence with the specified structural map.
-/
theorem exists_weierstrass_henselian_cylinder
    (Λ : Type u) [CommRing Λ] [IsDomain Λ] [IsNoetherianRing Λ] [IsLocalRing Λ]
    [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] (s : ℕ)
    (f : PowerSeries (MvPowerSeries (Fin s) Λ))
    (hf : f ∈ IsLocalRing.maximalIdeal (PowerSeries (MvPowerSeries (Fin s) Λ)))
    (hred : f ∉ Ideal.map (algebraMap Λ (PowerSeries (MvPowerSeries (Fin s) Λ)))
      (IsLocalRing.maximalIdeal Λ)) :
    ∃ (c : PowerSeries (MvPowerSeries (Fin s) Λ) ≃ₐ[PowerSeries Λ]
        PowerSeries (MvPowerSeries (Fin s) Λ))
      (N : Fin s → ℕ) (g : Polynomial (MvPowerSeries (Fin s) Λ))
      (unit : (PowerSeries (MvPowerSeries (Fin s) Λ))ˣ),
      (∀ i : Fin s, 0 < N i) ∧
      (∀ i : Fin s, c (PowerSeries.C (MvPowerSeries.X i)) =
        PowerSeries.C (MvPowerSeries.X i) + PowerSeries.X ^ N i) ∧
      (∀ n : ℕ, ∃ m : ℕ,
        ∀ x ∈ IsLocalRing.maximalIdeal (PowerSeries (MvPowerSeries (Fin s) Λ)) ^ m,
          c x ∈ IsLocalRing.maximalIdeal (PowerSeries (MvPowerSeries (Fin s) Λ)) ^ n) ∧
      (s = 0 → c = AlgEquiv.refl) ∧
      c f = (unit : PowerSeries (MvPowerSeries (Fin s) Λ)) * (g : PowerSeries _) ∧
      g.Monic ∧ 0 < g.natDegree ∧
      (∀ i : ℕ, i < g.natDegree →
        g.coeff i ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin s) Λ)) ∧
      ∃ (q : Ideal (Polynomial (MvPowerSeries (Fin s) Λ))),
        q = Ideal.comap Polynomial.constantCoeff
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin s) Λ)) ∧
        ∃ (_hq : q.IsPrime),
          ∀ (H : Type v) [CommRing H] [HenselianLocalRing H]
            [Algebra (Localization.AtPrime q) H],
            Algebra.IsHenselizationAtPrime' (Polynomial (MvPowerSeries (Fin s) Λ)) q H →
            IsNoetherianRing H ∧
            ∃ (a : Polynomial (MvPowerSeries (Fin s) Λ) →+* H),
              a = (algebraMap (Localization.AtPrime q) H).comp
                (algebraMap (Polynomial (MvPowerSeries (Fin s) Λ)) (Localization.AtPrime q)) ∧
              (∃ e : (MvPowerSeries (Fin s) Λ ⧸
                  IsLocalRing.maximalIdeal (MvPowerSeries (Fin s) Λ)) ≃+*
                  IsLocalRing.ResidueField H,
                e.toRingHom.comp (Ideal.Quotient.mk _) =
                  ((IsLocalRing.residue H).comp a).comp Polynomial.C) ∧
              HenselianRing H (Ideal.span {a g}) ∧
              ∃ φ : H →+* PowerSeries (MvPowerSeries (Fin s) Λ),
                IsLocalHom φ ∧ φ.comp a = Polynomial.coeToPowerSeries.ringHom ∧
                φ.FaithfullyFlat ∧
                (∃ e : AdicCompletion (Ideal.span {a g}) H ≃+*
                    PowerSeries (MvPowerSeries (Fin s) Λ),
                  e.toRingHom.comp (algebraMap H (AdicCompletion (Ideal.span {a g}) H)) = φ) ∧
                (∃ e : AdicCompletion (IsLocalRing.maximalIdeal H) H ≃+*
                    PowerSeries (MvPowerSeries (Fin s) Λ),
                  e.toRingHom.comp
                    (algebraMap H (AdicCompletion (IsLocalRing.maximalIdeal H) H)) = φ) := by
  sorry

end RingTheory
