module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.KrullDimension.PID
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import Sheaf.RingTheory.TameTraitInvariantKummerPresentation
import Sheaf.AlgebraicGeometry.TraitKummerDivisorialLogEtale
import Sheaf.AlgebraicGeometry.FSLogSmoothCompositionStrictBaseChange

/-!
# Tame quotients of complete strictly henselian traits

Source: ILO, Exposé XVI 3.7, printed p.254; Exposé VI 2.1--2.2, pp.71--72
(blueprint: lem-per-tame-trait-quotient-log-etale).

The quotient ring is Mathlib's actual fixed subalgebra. Its two scheme maps are
spectra of the coefficient map and the inclusion. Canonical log structures are
identified, over their structural maps, with the divisorial presheaves of the
fraction-field inclusions. Thus the log morphism is determined by pullback of
functions. No faithful-action hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A tame quotient is again a complete strictly henselian trait; the canonical
quotient map is finite dominant and log étale, its fraction-field degree divides
the group order, and every log-smooth scheme over the source stays log smooth
over the quotient. Source: ILO XVI 3.7, p.254; VI 2.1--2.2, pp.71--72
(blueprint: lem-per-tame-trait-quotient-log-etale).

Proof plan:
1. Put A = B^H. It is a finite R-module by the Noetherian submodule theorem
   (lem-weil-pbc-noetherian-submodule-finite). The same R-generators of B generate
   B over A. Finiteness implies integrality and contraction of maximal ideals
   (lem-weil-pbc-finite-algebra-is-integral,
   lem-weil-pbc-integral-maximal-contracts-maximal).
2. Extend the action to Frac B and replace H by its faithful image G. Invariant
   denominators show Frac A = (Frac B)^G
   (lem-sfb-finite-invariant-fraction-field-lifting). Fixed-field theory gives
   [Frac B : Frac A] = |G| dividing |H| (lem-wf-finite-field-action-fixed-degree).
3. Restrict the DVR valuation of B to Frac A. Its positive value subgroup has a
   least positive generator since it contains the valuation of a uniformizer of R.
   The nonnegative-valuation criterion identifies A with the resulting valuation
   ring. Choosing least valuations in ideals proves it is a DVR; the valuation
   sum rule proves B is its integral closure (def-sc-discrete-valuation-ring,
   lem-sc-dvr-nonnegative-valuation-in-ring, lem-sc-dvr-valuation-arithmetic).
4. Finiteness over complete R gives completeness and locality of A
   (lem-weil-pbc-finite-over-complete-local-product); completeness gives henselianity
   and hence simple-root lifting (lem-weil-pbc-complete-pair-henselian,
   lem-weil-pbc-henselian-local-root-lifting).
5. The finite residue extension of the separably closed residue field of R is
   purely inseparable (lem-kun-sep-closed-finite-extension-purely-inseparable),
   so H acts trivially on it. Averaging a lift by the invertible order of H
   identifies the residue fields of A and B. Thus A is strictly henselian.
   The two injective finite ring maps give finite dominant spectrum maps.
6. The Galois degree formula (lem-exc-dvr-galois-degree-data), with one prime
   and residue degree one, makes the ramification index n equal the field degree.
7. Write pi = unit * t^n. Simple-root lifting extracts an nth root of the unit,
   yielding tau^n = pi. The totally ramified uniformizer presentation
   (lem-sfb-totally-ramified-uniformizer-presentation) gives B = A[tau] and
   B = A[X]/(X^n-pi).
8. Uniformizers chart the canonical divisorial structures: sections and strict
   stalks agree (lem-weil-pbc-sets-strictly-henselian-open-sections-stalk),
   and every nonzero DVR element is a unit times a uniformizer power.
   The compatible chart is N --times n--> N, with zero kernel and invertible
   finite cokernel. Its comparison is the preceding affine isomorphism
   (lem-weil-pbc-fibre-product-affine-spectra), hence étale. Apply the log-étale
   chart definition (def-per-fs-log-smooth-etale, def-trf-fs-log-blowup).
9. Log étale implies log smooth and log-smooth morphisms compose
   (lem-sfb-log-smooth-composition-strict-base-change), proving the universal clause.
-/
theorem tame_trait_quotient_logEtale
    (R B : Type u) [CommRing R] [CommRing B] [IsDomain R] [IsDomain B]
    [IsNoetherianRing R] [IsNoetherianRing B]
    [IsStrictlyHenselianLocalRing R] [IsStrictlyHenselianLocalRing B]
    (hRdim : ringKrullDim R = 1) (hBdim : ringKrullDim B = 1)
    (hRprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal)
    (hBprincipal : (IsLocalRing.maximalIdeal B).IsPrincipal)
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [CharZero (FractionRing R)] [CharZero (FractionRing B)]
    (hRchar : ringChar (IsLocalRing.ResidueField R) ≠ 0)
    (hBchar : ringChar (IsLocalRing.ResidueField B) ≠ 0)
    [Algebra R B]
    [IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (hdominant : DenseRange (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (H : Type v) [Group H] [Finite H] [MulSemiringAction H B] [SMulCommClass H R B]
    (horder : IsUnit (Nat.card H : R)) :
    IsNoetherianRing (FixedPoints.subalgebra R B H) ∧
    ringKrullDim (FixedPoints.subalgebra R B H) = 1 ∧
    (∃ hA : IsStrictlyHenselianLocalRing (FixedPoints.subalgebra R B H),
      (@IsLocalRing.maximalIdeal (FixedPoints.subalgebra R B H) _
        hA.toIsLocalRing).IsPrincipal ∧
      IsAdicComplete (@IsLocalRing.maximalIdeal (FixedPoints.subalgebra R B H) _
        hA.toIsLocalRing) (FixedPoints.subalgebra R B H)) ∧
    IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap R (FixedPoints.subalgebra R B H)))) ∧
    DenseRange (Spec.map (CommRingCat.ofHom
      (algebraMap R (FixedPoints.subalgebra R B H)))) ∧
    IsFinite (Spec.map (CommRingCat.ofHom (FixedPoints.subalgebra R B H).val.toRingHom)) ∧
    DenseRange (Spec.map (CommRingCat.ofHom (FixedPoints.subalgebra R B H).val.toRingHom)) ∧
    (@Module.finrank (FractionRing (FixedPoints.subalgebra R B H)) (FractionRing B) _ _
      (FractionRing.liftAlgebra (FixedPoints.subalgebra R B H) (FractionRing B)).toModule
      ∣ Nat.card H) ∧
    ∃ (SB T : FineSaturatedLogScheme.{u})
      (eB : SB.scheme ≅ Spec (.of B))
      (eT : T.scheme ≅ Spec (.of (FixedPoints.subalgebra R B H)))
      (q : EtaleLogHom SB T),
      (∃ e : SB.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf
          (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫ eB.inv),
        e.hom ≫ divisorialStructuralMap
          (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫ eB.inv) =
            SB.logStructure.alpha) ∧
      (∃ e : T.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf
          (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R B H)
            (FractionRing (FixedPoints.subalgebra R B H)))) ≫ eT.inv),
        e.hom ≫ divisorialStructuralMap
          (Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R B H)
            (FractionRing (FixedPoints.subalgebra R B H)))) ≫ eT.inv) =
              T.logStructure.alpha) ∧
      q.base ≫ eT.hom = eB.hom ≫
        Spec.map (CommRingCat.ofHom (FixedPoints.subalgebra R B H).val.toRingHom) ∧
      q.IsLogEtale ∧
      ∀ (V : FineSaturatedLogScheme.{u}) (f : EtaleLogHom V SB), f.IsLogSmooth →
        ∃ c : EtaleLogHom V T, f.CompEq q c ∧ c.IsLogSmooth := by
  classical
  let A := FixedPoints.subalgebra R B H
  have hRB : (algebraMap R B).Finite :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R B))).mp inferInstance
  let : Module.Finite R B := RingHom.finite_algebraMap.mp hRB
  have hinj : Function.Injective (algebraMap R B) := by
    have hk := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mp hdominant
    rw [nilradical_eq_zero] at hk
    exact (RingHom.injective_iff_ker_eq_bot _).mpr (le_antisymm hk bot_le)
  let : Module.Finite R A := Module.Finite.of_injective
    (FixedPoints.subalgebra R B H).val.toLinearMap Subtype.val_injective
  have hAN : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  have hRA : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R A))).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  have hAB : IsFinite (Spec.map (CommRingCat.ofHom
      (FixedPoints.subalgebra R B H).val.toRingHom)) := by
    apply (IsFinite.SpecMap_iff
      (CommRingCat.ofHom (FixedPoints.subalgebra R B H).val.toRingHom)).mpr
    exact RingHom.Finite.of_comp_finite (f := algebraMap R A) (by simpa using hRB)
  have hAinj : Function.Injective (algebraMap R A) := by
    intro x y h
    apply hinj
    exact congrArg (fun a : A ↦ (a : B)) h
  have hRAdense : DenseRange (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    change RingHom.ker (algebraMap R A) ≤ nilradical R
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hAinj]
    exact bot_le
  have hABdense : DenseRange (Spec.map (CommRingCat.ofHom
      (FixedPoints.subalgebra R B H).val.toRingHom)) := by
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    change RingHom.ker (FixedPoints.subalgebra R B H).val.toRingHom ≤ nilradical A
    rw [(RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
    exact bot_le
  have hRfield : ¬ IsField R :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hRdim).1
  have hBfield : ¬ IsField B :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hBdim).1
  let : IsDiscreteValuationRing R := (IsDiscreteValuationRing.TFAE R hRfield).out
    4 0 |>.mp hRprincipal
  let : IsDiscreteValuationRing B := (IsDiscreteValuationRing.TFAE B hBfield).out
    4 0 |>.mp hBprincipal
  obtain ⟨hAD, hAS, n, hn, hndvd, hdegree, hunit, pi, tau, hpi, htau, hpow, e, he⟩ :=
    tame_trait_invariant_kummer_presentation R B hRchar hBchar hinj H horder
  let : IsDiscreteValuationRing A := hAD
  let : IsStrictlyHenselianLocalRing A := hAS
  have hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
    obtain ⟨_, hL, hc, _⟩ :=
      (Algebra.finite_over_complete_local_product R A).2.2.2 inferInstance
    exact hc
  obtain ⟨SB, T, eB, eT, q, hcanB, hcanA, hqbase, hqetale⟩ :=
    trait_kummer_divisorial_logEtale A B Subtype.val_injective n hn hunit
      pi hpi tau htau hpow e he
  refine ⟨hAN, IsPrincipalIdealRing.ringKrullDim_eq_one A ?_,
    ⟨hAS, inferInstance, hAc⟩, hRA, hRAdense, hAB, hABdense, ?_,
    SB, T, eB, eT, q, hcanB, hcanA, hqbase, hqetale, ?_⟩
  · exact fun h ↦ IsDiscreteValuationRing.not_a_field A
      (IsLocalRing.isField_iff_maximalIdeal_eq.mp h)
  · rwa [hdegree]
  · intro V f hf
    exact fsLogSmooth_composition_strictBaseChange.{u, 0}.1 V SB T f q hf
      (fsLogSmooth_composition_strictBaseChange.{u, 0}.2.1 SB T q hqetale)

end AlgebraicGeometry
