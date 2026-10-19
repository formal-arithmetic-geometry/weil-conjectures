/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q37 and Q7
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Ideal
import Sheaf.RingTheory.RegularRingSmoothAscent
import Sheaf.RingTheory.GenericSmoothDomain

/-!
# Ascent of a nonempty regular open for separable fraction fields

Source: Stacks Project, More on Algebra, Tag 07PB, lemma-J-0-goes-up, with J-0 expanded
using Tag 07P7, definition-J; separability is Algebra, Tag 030O
(blueprint: lem-exc-j0-separable-finite-type-ascent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- A nonempty regular open ascends along an injective finite type map of domains over a
Noetherian base when the induced fraction-field extension is separable in the sense of
Stacks Tag 030O. The algebra structure in `hsep` is the canonical map on fraction fields,
not an independently chosen field embedding.

Source: Stacks Project, More on Algebra, Tag 07PB, lemma-J-0-goes-up; Tag 07P7,
definition-J (blueprint: lem-exc-j0-separable-finite-type-ascent).

Proof:
1. The basic opens form a basis, so choose a nonzero f with D(f) inside the given
   nonempty regular open U. Every prime of A = R_f contracts into D(f), and its local
   ring is canonically the localization of R at the contracted prime. Thus A is regular;
   its Noetherianity follows by localization.
2. Apply generic smoothness to the original map R → S, obtaining g ≠ 0 such that
   C = S_g is smooth over R. Put T = C_image(f). This is smooth over R by composition.
3. Since f is a unit in T, the R-algebra structure factors through A. Formal smoothness
   over R implies formal smoothness over A: every R-algebra lift automatically respects
   inverses of f. Finite type over R implies finite type over A, and A is Noetherian,
   hence T is finitely presented over A. Therefore T is smooth over the regular ring A,
   and regularity ascent makes T regular.
4. Set a = image(f) * g ≠ 0. The composite localization T is a localization of S at a.
   For q in D(a), its extension Q to T is prime and contracts to q. Localizing T at Q
   is therefore also a localization of S at q, giving T_Q ≃ S_q. Transport regularity
   along this equivalence. Finally D(a) is nonempty because it contains the zero prime.

This is the principal-localization argument of the source, applying generic smoothness
before localizing the base to avoid transporting the separability hypothesis between
canonically isomorphic fraction fields.
-/
theorem exists_nonempty_open_regular_of_separable_fractionRing
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsDomain R] [IsDomain S] [Algebra R S] [FiniteType R S]
    (hinj : Function.Injective (algebraMap R S))
    (hsep : @IsSeparableExtension (FractionRing R) (FractionRing S) _ _
      (IsFractionRing.map (K := FractionRing R) (L := FractionRing S) hinj).toAlgebra)
    (hregular : ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, IsRegularLocalRing (Localization.AtPrime p.asIdeal)) :
    ∃ V : Set (PrimeSpectrum S), IsOpen V ∧ V.Nonempty ∧
      ∀ q ∈ V, IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  classical
  obtain ⟨U, hU, ⟨p, hp⟩, hreg⟩ := hregular
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hU p hp
  have hf : f ≠ 0 := by
    intro hf
    exact hpf (hf ▸ p.asIdeal.zero_mem)
  let A := Localization.Away f
  have hA : IsRegularRing A := by
    apply isRegularRing_iff.mpr
    intro P hP
    let p' : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) ⟨P, hP⟩
    have hfp' : p' ∈ PrimeSpectrum.basicOpen f := by
      intro h
      exact hP.ne_top (P.eq_top_of_isUnit_mem h
        (IsLocalization.Away.algebraMap_isUnit f))
    have : IsRegularLocalRing (Localization.AtPrime (P.comap (algebraMap R A))) :=
      hreg p' (hfU hfp')
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (Submonoid.powers f) P).toRingEquiv
  have : IsRegularRing A := hA
  obtain ⟨g, hg, hsm⟩ :=
    exists_smooth_localization_of_separable_fractionRing R S hinj hsep
  let C := Localization.Away g
  have : Smooth R C := hsm
  let T := Localization.Away (algebraMap R C f)
  have : Smooth C T := Smooth.of_isLocalization_Away (algebraMap R C f)
  have : Smooth R T := Smooth.comp R C T
  have hunit : IsUnit (algebraMap R T f) := by
    rw [IsScalarTower.algebraMap_apply R C T]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R C f)
  let : Algebra A T := (IsLocalization.Away.lift f hunit).toAlgebra
  have : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq' (by
    exact (IsLocalization.Away.lift_comp f hunit).symm)
  have : FormallySmooth A T := FormallySmooth.localization_base (Submonoid.powers f)
  have : FiniteType A T := FiniteType.of_restrictScalars_finiteType R A T
  have : FinitePresentation A T := FinitePresentation.of_finiteType.mp inferInstance
  have : Smooth A T := ⟨inferInstance, inferInstance⟩
  have : IsRegularRing T := isRegularRing_of_smooth A T
  let a : S := algebraMap R S f * g
  have ha : a ≠ 0 := mul_ne_zero (fun h => hf (hinj (h.trans (map_zero _).symm))) hg
  have hloc : IsLocalization.Away a T := by
    apply IsLocalization.Away.mul C T g (algebraMap R S f)
  have : IsLocalization.Away a T := hloc
  refine ⟨PrimeSpectrum.basicOpen a, (PrimeSpectrum.basicOpen a).isOpen, ?_, ?_⟩
  · exact ⟨⟨⊥, Ideal.isPrime_bot⟩, ha⟩
  · intro q hq
    have hd : Disjoint (Submonoid.powers a : Set S) (q.asIdeal : Set S) :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime a).mpr hq
    let Q := q.asIdeal.map (algebraMap S T)
    have hQ : Q.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) T
        q.asIdeal q.isPrime hd
    have hc : Q.comap (algebraMap S T) = q.asIdeal :=
      IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) T q.isPrime hd
    have : IsRegularLocalRing (Localization.AtPrime Q) := inferInstance
    have : IsLocalization.AtPrime (Localization.AtPrime Q) q.asIdeal := by
      simpa only [hc] using
        (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
          (Submonoid.powers a) (Localization.AtPrime Q) Q)
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.asIdeal.primeCompl
        (Localization.AtPrime Q) (Localization.AtPrime q.asIdeal)).toRingEquiv

end Algebra
