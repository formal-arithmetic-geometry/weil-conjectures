/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import Sheaf.RingTheory.IntegralComponentHenselianPermanence
import Sheaf.TraceFormula.HenselizationPrimeIndEtale
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.RingTheory.Etale.QuasiFiniteAtPrime
import Sheaf.RingTheory.EtaleColimitNormalLocalDomain
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Etale.Field
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Internal finite normalization of a nonlocal henselian join

Source: Hübner--Schmidt, The tame site of a scheme, proof of Theorem 6.3,
printed p. 13, and the agent-formulated internal-normalization refinement in the DAG
(blueprint: lem-trf-nonlocal-join-internal-normalization).

The fraction field of the embedded join is represented by its subfield closure in
`Ω`. The enlarged henselizations are subalgebras of the same fixed `Ω`, so their
inclusions, their containment in the join, and equality of generated rings are literal.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Algebra

/-- A normal henselian join whose two factor embeddings are nonlocal admits a finite
separable normalization inside its own fraction field, with incomparable centers and
compatible enlarged henselizations generating exactly the original join.
Source: Hübner--Schmidt, proof of Theorem 6.3, printed p. 13; the internal refinement
and its full argument are agent-formulated in the DAG
(blueprint: lem-trf-nonlocal-join-internal-normalization).

Here `Subfield.closure (J : Set Ω)` is `Frac(J)` inside `Ω`. The equality
`P0 = integralClosure P K0` specifies the actual normalization, rather than an
arbitrary normal algebra. The maps from its prime localizations into `H0 i` agree
in `Ω` with the canonical inclusion of `P0` into `K0`. The maps `u` extend the
prescribed embeddings of the original henselizations.

Proof:
1. Inside L = Frac(J), form B = icl_P(L) and S_i = icl_{H_i}(L). Each S_i is a
   nonzero domain and has only the idempotents 0 and 1. Apply
   lem-trf-integral-component-henselian-permanence: S_i is henselian local and
   H_i → S_i is local.
2. A monic equation over H_i is one over J. Normality of J puts S_i inside J.
   Also B lies in S_i. Contract the maximal ideal of S_i to a prime r_i of B;
   its contraction to P is q_i by locality of the henselization maps.
3. Algebraicity of L/K and clearing coefficient denominators show every x in L
   is (dx)/d with dx integral over P. Thus Frac(B) = L. Transitivity of integrality
   (lem-weil-pbc-integral-transitive) then proves B normal.
4. Write H_i as a filtered colimit of etale P-algebras using
   lem-trf-henselization-prime-ind-etale and def-weil-pbc-ind-etale-algebra.
   Represent h by e in a stage E using lem-weil-pbc-filtered-colimit-algebras-elementwise.
   At the prime contracted from S_i, apply lem-weil-pbc-etale-ring-map-quasi-finite
   and lem-weil-pbc-integral-closure-zariski-main-away to E itself.
5. The resulting localization equality writes e = c/g^n, with c and g integral
   over P and g outside the contracted prime. Their images in L lie in B and
   g avoids r_i. Hence H_i lies in B_{r_i}, while B_{r_i} lies in S_i.
6. By lem-weil-pbc-localization-normal-domain, B_{r_i} is normal with fraction
   field L. Every element of S_i is integral over its subring H_i, hence over
   B_{r_i}; normality gives S_i = B_{r_i}.
7. If r_1 ≤ r_2, then S_2 lies in S_1. Consequently S_1 contains both H_i,
   hence J, and S_1 = J. This contradicts nonlocality of H_1 → J. Reverse the
   indices to exclude the other containment.
8. Choose a in r_1 outside r_2 and b in r_2 outside r_1. The internal field
   K0 = K(a,b) is finite separable: a and b lie in the separable closure, and
   bounded powers span a finite-dimensional domain, which is a field. Put
   P0 = B ∩ K0 and contract r_i to q0_i. The elements a and b witness incomparability.
9. P0 is the actual integral closure of P in K0. Repeat denominator clearing
   to show Frac(P0) = K0, and use transitivity of integrality to prove normality.
10. The inclusions P0 → S_i extend to injective local maps R_i = (P0)_{q0_i} → S_i.
    The henselization universal property gives local maps H0_i = R_i^h → S_i.
11. R_i is normal by lem-weil-pbc-localization-normal-domain. Express H0_i as an
    etale colimit using lem-trf-henselization-prime-ind-etale, identifying localization
    at the maximal ideal of R_i with R_i. Apply
    lem-weil-pbc-etale-colimit-normal-local-domain to obtain normality of H0_i and
    injectivity of R_i → H0_i.
12. Represent an element of H0_i at an etale stage. Base change to K0 using
    lem-weil-pbc-etale-ring-base-change; then
    lem-weil-pbc-etale-algebra-over-field-product gives a finite product of finite
    separable fields. The product of their annihilating polynomials proves the
    element algebraic over K0.
13. If a nonzero element of H0_i maps to zero in S_i, remove the initial power
    of T from an annihilating polynomial and clear denominators. Its nonzero
    constant coefficient would map to zero in S_i, contradicting injectivity
    of R_i → S_i. Thus H0_i embeds into S_i, and hence into J and Ω.
14. Locality of P_{q_i} → R_i gives a local map u_i : H_i → H0_i. Uniqueness
    in the henselization universal property, with target S_i, identifies its
    composite with the prescribed H_i → S_i. Thus u_i is injective and the
    embeddings into Ω are compatible.
15. The enlarged images lie in J and contain the two original images.
    Their generated subring therefore equals J by the two containments. -/
theorem exists_internal_normalization_of_nonlocal_join
    (P : Type u) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    (K : Type v) [Field K] [Algebra P K] [IsFractionRing P K]
    (Ω : Type w) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra P Ω] [IsScalarTower P K Ω]
    (q : Fin 2 → PrimeSpectrum P)
    (H : Fin 2 → Type z) [∀ i, CommRing (H i)]
    [∀ i, Algebra (Localization.AtPrime (q i).asIdeal) (H i)]
    [∀ i, HenselianLocalRing (H i)] [∀ i, Algebra P (H i)]
    [∀ i, IsScalarTower P (Localization.AtPrime (q i).asIdeal) (H i)]
    (hH : ∀ i, IsHenselizationAtPrime' P (q i).asIdeal (H i))
    (J : Subalgebra P Ω) [HenselianLocalRing J] [IsIntegrallyClosed J]
    (e : ∀ i, H i →ₐ[P] J) (he : ∀ i, Function.Injective (e i))
    (hgen : Subring.closure (⋃ i, Set.range (J.val.comp (e i))) = J.toSubring)
    (hnonlocal : ∀ i, Ideal.comap (e i).toRingHom (IsLocalRing.maximalIdeal J) <
      IsLocalRing.maximalIdeal (H i)) :
    ∃ (K0 : IntermediateField K Ω) (P0 : Subalgebra P K0)
      (q0 : Fin 2 → PrimeSpectrum P0) (H0 : Fin 2 → Subalgebra P Ω)
      (a0 : ∀ i, Algebra (Localization.AtPrime (q0 i).asIdeal) (H0 i))
      (h0 : ∀ i, HenselianLocalRing (H0 i)) (u0 : ∀ i, H i →ₐ[P] H0 i),
      K0.toSubfield ≤ Subfield.closure (J : Set Ω) ∧
      FiniteDimensional K K0 ∧ Algebra.IsSeparable K K0 ∧
      P0 = integralClosure P K0 ∧
      (IsDomain P0 ∧ IsIntegrallyClosed P0) ∧ IsFractionRing P0 K0 ∧
      (∀ i, Ideal.comap (algebraMap P P0) (q0 i).asIdeal = (q i).asIdeal) ∧
      (¬ (q0 0).asIdeal ≤ (q0 1).asIdeal) ∧ (¬ (q0 1).asIdeal ≤ (q0 0).asIdeal) ∧
      (∀ i, @IsHenselizationAtPrime' P0 _ (q0 i).asIdeal (H0 i) _ _ (a0 i) (h0 i)) ∧
      (∀ i (x : P0),
        ((@algebraMap (Localization.AtPrime (q0 i).asIdeal) (H0 i) _ _ (a0 i)
          (algebraMap P0 (Localization.AtPrime (q0 i).asIdeal) x) : H0 i) : Ω) =
          algebraMap K0 Ω (x : K0)) ∧
      (∀ i, H0 i ≤ J) ∧
      (∀ i, Function.Injective (u0 i)) ∧
      (∀ i, (H0 i).val.comp (u0 i) = J.val.comp (e i)) ∧
      Subring.closure (⋃ i, Set.range (H0 i).val) = J.toSubring := by
  sorry

end Algebra
