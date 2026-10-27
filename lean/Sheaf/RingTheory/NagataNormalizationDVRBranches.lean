module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Ring.Pi
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Mathlib.RingTheory.Localization.Integral
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DedekindDomain.Dvr

/-! # Finite normalization and DVR branches of a reduced Nagata curve ring

Source: Stacks Project, Varieties, Tags 0C3S and 0C3V, component normalization and
local DVR input (no completion assertion).
(blueprint: lem-trf-nagata-normalization-dvr-branches)
-/

@[expose] public section

universe u

/-- The normalization of a reduced one-dimensional local Nagata ring is the finite
product of the Dedekind normalizations of its minimal-prime quotients. Its primes
above the maximal ideal select unique nonzero maximal component primes, with
canonical localization isomorphisms, and those localizations are DVRs.

The maps `f` are the canonical maps from the domain quotients to the minimal-prime
localizations, specified by their composites with the quotient maps. The subalgebras
`E` are explicitly required to be their integral closures. The equivalence `eQ` is
an A-algebra equivalence, and the displayed coordinate identity requires `eB` to
be its restriction. The localization equivalences commute with the projections.

Source: Stacks Project, Varieties, Tags 0C3S and 0C3V; Algebra, Tags 032R,
032F, 00FR, 00FN, 02LX, 00EU, 00EW, 034L, 00OK, 00GS, 034X, 00PD.
(blueprint: lem-trf-nagata-normalization-dvr-branches)

Proof:
1. Nagata implies Noetherian. By lem-weil-pbc-noetherian-finitely-many-minimal-primes,
   enumerate all distinct minimal primes. None is maximal, since dimension is one.
   Quotient ideal correspondence makes each quotient a one-dimensional local domain;
   lem-weil-pbc-surjective-image-noetherian makes it Noetherian. Its prime quotients
   are prime quotients of A, hence N-2, so it is Nagata.
2. By lem-weil-pbc-reduced-noetherian-total-ring-fractions the total fraction ring is
   the product of the minimal-prime localizations, which are fields. Their maps from A
   have kernels the minimal primes. The induced maps from the quotients are injective,
   and every localized element is a quotient of images, giving their fraction fields.
3. Apply def-weil-pbc-japanese-domain to the identity extension of each fraction field:
   its integral closure is finite. By lem-weil-pbc-finite-algebra-noetherian and
   lem-weil-pbc-integral-closure-finite-extension-normal it is a Noetherian normal domain.
   By lem-weil-pbc-integral-injective-dimension-equal its dimension is one.
4. Projecting a monic equation gives coordinatewise integrality. Conversely lift a monic
   equation from each quotient to A and multiply these polynomials: their product is
   monic and annihilates the tuple. Thus eQ restricts to the stated eB.
5. Take finite generators of each component normalization over its domain quotient.
   Their supported tuples generate the product over A after lifting coefficients,
   proving that the normalization is a finite A-module.
6. For a prime q of the product exactly one coordinate idempotent lies outside q:
   their sum is one and their pairwise products are zero. The projection kernel is
   contained in q, giving the unique component prime r and its stated contraction.
   The fraction map b/s to b_i/s_i identifies the localizations: all other idempotents
   vanish after localization, so the supported-coordinate inverse is unital.
7. By lem-weil-pbc-integral-prime-over-maximal-maximal, r is maximal. It is nonzero
   because its contraction is the nonzero maximal ideal of the domain quotient.
   By lem-sc-dedekind-localization-dvr its localization, and therefore B_q, is a DVR.
-/
theorem nagata_normalization_dvr_branches
    (A : Type u) [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : IsNagataRing A) (hdim : ringKrullDim A = 1) :
    ∃ t : ℕ, ∃ p : Fin t ≃ {p : PrimeSpectrum A // p.asIdeal ∈ minimalPrimes A},
      ∃ f : ∀ i : Fin t, (A ⧸ (p i).val.asIdeal) →+*
        Localization.AtPrime (p i).val.asIdeal,
      ∃ E : ∀ i : Fin t,
        @Subalgebra (A ⧸ (p i).val.asIdeal) (Localization.AtPrime (p i).val.asIdeal)
          _ _ (f i).toAlgebra,
      ∃ eQ : FractionRing A ≃ₐ[A] (∀ i : Fin t, Localization.AtPrime (p i).val.asIdeal),
      ∃ eB : integralClosure A (FractionRing A) ≃+* (∀ i : Fin t, E i),
        (∀ i : Fin t, (f i).comp (Ideal.Quotient.mk (p i).val.asIdeal) =
          algebraMap A (Localization.AtPrime (p i).val.asIdeal)) ∧
        (∀ i : Fin t, E i =
          @integralClosure (A ⧸ (p i).val.asIdeal)
            (Localization.AtPrime (p i).val.asIdeal) _ _ (f i).toAlgebra) ∧
        (∀ i : Fin t,
          IsDomain (A ⧸ (p i).val.asIdeal) ∧
          IsNoetherianRing (A ⧸ (p i).val.asIdeal) ∧
          IsLocalRing (A ⧸ (p i).val.asIdeal) ∧
          IsNagataRing (A ⧸ (p i).val.asIdeal) ∧
          ringKrullDim (A ⧸ (p i).val.asIdeal) = 1 ∧
          IsField (Localization.AtPrime (p i).val.asIdeal) ∧
          @IsFractionRing (A ⧸ (p i).val.asIdeal) _
            (Localization.AtPrime (p i).val.asIdeal) _ (f i).toAlgebra) ∧
        (∀ i : Fin t, Module.Finite (A ⧸ (p i).val.asIdeal) (E i) ∧
          IsDomain (E i) ∧ IsNoetherianRing (E i) ∧ IsIntegrallyClosed (E i) ∧
          ringKrullDim (E i) = 1) ∧
        (∀ (b : integralClosure A (FractionRing A)) (i : Fin t),
          (eB b i : Localization.AtPrime (p i).val.asIdeal) = eQ b.val i) ∧
        Module.Finite A (integralClosure A (FractionRing A)) ∧
        (∀ q : PrimeSpectrum (integralClosure A (FractionRing A)),
          q.asIdeal.comap (algebraMap A (integralClosure A (FractionRing A))) =
            IsLocalRing.maximalIdeal A →
          (∃! z : Σ i : Fin t, PrimeSpectrum (E i),
            q.asIdeal = z.2.asIdeal.comap
              ((Pi.evalRingHom (fun i ↦ E i) z.1).comp eB.toRingHom) ∧
            z.2.asIdeal.IsMaximal ∧ z.2.asIdeal ≠ ⊥ ∧
            z.2.asIdeal.comap (algebraMap (A ⧸ (p z.1).val.asIdeal) (E z.1)) =
              (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk (p z.1).val.asIdeal) ∧
            ∃ e : Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime z.2.asIdeal,
              e.toRingHom.comp (algebraMap _ (Localization.AtPrime q.asIdeal)) =
                (algebraMap (E z.1) (Localization.AtPrime z.2.asIdeal)).comp
                  ((Pi.evalRingHom (fun i ↦ E i) z.1).comp eB.toRingHom)) ∧
          ∃ hq : IsDomain (Localization.AtPrime q.asIdeal),
            @IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) _ hq) := by
  sorry
