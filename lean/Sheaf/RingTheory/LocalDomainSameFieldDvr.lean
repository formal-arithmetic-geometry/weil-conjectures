module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Sheaf.RingTheory.LocalDomainBirationalDimensionOne
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# A dominating DVR inside the prescribed fraction field

Source: Stacks Project, Algebra, Tag 00PH, specialized to the identity field extension.
(blueprint: lem-sfb-local-domain-same-field-dvr).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsLocalRing

/-- A nonfield Noetherian local domain has a dominating discrete valuation subring
inside its specified fraction field. The subalgebra packages the subring and its
containment of the image of the original domain.

Source: Stacks Project, Algebra, Tag 00PH (identity extension of fraction fields).
(blueprint: lem-sfb-local-domain-same-field-dvr).

Proof:
1. Apply `lem-sfb-local-domain-birational-dimension-one` (Tag 00P8) to obtain
   a Noetherian local domain R inside K, containing B, of dimension one, whose
   maximal ideal contracts to the maximal ideal of B. Its fraction field is K.
2. Let C be the integral closure of R in K. Apply
   `lem-sc-integral-closure-dedekind-surjective-fibres` (Tag 09IG) to the identity
   finite extension K/K. Then C is Noetherian, integrally closed and dimension one,
   and its spectrum surjects onto that of R. Choose a prime q of C over the maximal
   ideal of R. Since B is contained in R and C inside K, every element of K is
   still a ratio of elements of C, so K is the fraction field of C.
3. Apply clause (1) of `lem-weil-pbc-dim-one-residue-field-extensions-finite`
   (Tag 031F) to R inside C with fraction field extension K/K. The prime q is
   maximal. It is nonzero: a nonzero element of the maximal ideal of B stays
   nonzero in K and belongs to q by the contraction equalities.
4. Localize C at q. By `lem-weil-pbc-localization-normal-domain` (Tag 00GY),
   this localization embeds in K by the fraction formula and still has fraction
   field K. By `lem-sc-dedekind-localization-dvr` (Tag 034X), it is a DVR.
   Its image A in K is a subring containing B and hence a B-subalgebra of K.
5. The maximal ideal of the localization contracts to q: elements of q map into
   the maximal ideal, while an element outside q becomes a unit, with reciprocal
   as inverse. Contracting further to R and then B gives the asserted equality
   of maximal ideals. This equality also says that the inclusion B into A is local.
-/
theorem exists_dvr_subalgebra_same_fraction_field
    (B : Type u) (K : Type v) [CommRing B] [IsDomain B] [IsLocalRing B]
    [IsNoetherianRing B] [Field K] [Algebra B K] [IsFractionRing B K]
    (hB : ¬ IsField B) :
    ∃ (A : Subalgebra B K) (_ : IsDiscreteValuationRing A),
      IsFractionRing A K ∧
      (IsLocalRing.maximalIdeal A).comap (algebraMap B A) = IsLocalRing.maximalIdeal B ∧
      IsLocalHom (algebraMap B A) := by
  classical
  have hmB : maximalIdeal B ≠ ⊥ := fun h ↦
    hB (isField_iff_maximalIdeal_eq.mpr h)
  obtain ⟨R, hRN, hRL, hdim, hRB, hRK⟩ :=
    exists_birational_dimension_one_subalgebra B K hmB
  let C := integralClosure R K
  have hC : IsDedekindDomain C :=
    (AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres R K K hdim).1
  have : IsFractionRing C K :=
    integralClosure.isFractionRing_of_finite_extension K K
  obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R C
    ⟨maximalIdeal R, inferInstance⟩
  have hqR : q.asIdeal.comap (algebraMap R C) = maximalIdeal R :=
    congrArg PrimeSpectrum.asIdeal hq
  have hq0 : q.asIdeal ≠ ⊥ := by
    intro hzero
    have hinj := IsFractionRing.injective R K
    have hRC : Function.Injective (algebraMap R C) := by
      exact Function.Injective.of_comp (f := algebraMap C K) hinj
    have hmR : maximalIdeal R = ⊥ := by
      rw [← hqR, hzero, Ideal.comap_bot_of_injective _ hRC]
    have hz := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hmR)
    rw [hdim] at hz
    exact one_ne_zero hz
  let A₀ := Localization.subalgebra K q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsDiscreteValuationRing A₀ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hq0 A₀
  let f : B →+* A₀ :=
    (algebraMap C A₀).comp ((algebraMap R C).comp (algebraMap B R))
  have hAB : (maximalIdeal A₀).comap f = maximalIdeal B := by
    have hAC : (maximalIdeal A₀).comap (algebraMap C A₀) = q.asIdeal :=
      IsLocalization.AtPrime.under_maximalIdeal A₀ q.asIdeal
    rw [show f = (algebraMap C A₀).comp
      ((algebraMap R C).comp (algebraMap B R)) from rfl,
      ← Ideal.comap_comap, hAC, ← Ideal.comap_comap, hqR, hRB]
  refine ⟨(A₀.restrictScalars R).restrictScalars B, ?_, ?_, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing A₀)
  · exact inferInstanceAs (IsFractionRing A₀ K)
  · exact hAB
  · exact ((local_hom_TFAE f).out 4 0).mp hAB

end IsLocalRing
