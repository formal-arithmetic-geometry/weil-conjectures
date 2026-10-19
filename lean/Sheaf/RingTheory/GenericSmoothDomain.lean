/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
import all Sheaf.AlgebraicGeometry.GenericLocallyOfFinitePresentation
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Generic smoothness for a separable extension of fraction fields

Source: Stacks Project, Algebra, Lemma 10.42.2 (Tag 07ND), implication from
separable fraction fields to smoothness at the generic point (blueprint:
lem-exc-generic-smooth-domain).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- Generic finite presentation, allowing different universes via `Shrink`. -/
private theorem exists_generic_finitePresentation (R : Type u) (S : Type v)
    [CommRing R] [CommRing S]
    [IsDomain R] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ a : R, a ≠ 0 ∧
      Algebra.FinitePresentation R (Localization.Away (algebraMap R S a)) := by
  have : Small.{u} S := Algebra.FiniteType.small (R := R)
  let B := Shrink.{u} S
  let e : B ≃ₐ[R] S := Shrink.algEquiv R S
  have : Algebra.FiniteType R B := Algebra.FiniteType.equiv inferInstance e.symm
  obtain ⟨a, ha, hfp⟩ := RingHom.exists_nonzero_finitePresentation_localizationAway
    (algebraMap R B) (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : Algebra.FinitePresentation R (Localization.Away (algebraMap R B a)) := by
    exact RingHom.finitePresentation_algebraMap.mp (hfp _)
  refine ⟨a, ha, Algebra.FinitePresentation.equiv (A := Localization.Away (algebraMap R B a)) ?_⟩
  exact IsLocalization.algEquivOfAlgEquiv
    (Localization.Away (algebraMap R B a)) (Localization.Away (algebraMap R S a)) e
    (by simpa only [e.commutes] using Submonoid.map_powers e (algebraMap R B a))

/-- Apply separability to the top intermediate field, then use Mathlib. -/
private theorem formallySmooth_of_separable_essFiniteType {k : Type u} {L : Type v}
    [Field k] [Field L] [Algebra k L]
    [Algebra.EssFiniteType k L] (hsep : Algebra.IsSeparableExtension k L) :
    Algebra.FormallySmooth k L := by
  obtain ⟨s, hs, hsep⟩ := hsep ⊤ (IntermediateField.fg_top k L)
  have : Algebra.IsSeparable
      (IntermediateField.adjoin k (Set.range ((↑) : s → (⊤ : IntermediateField k L))))
      (⊤ : IntermediateField k L) := by
    have hr : Set.range ((↑) : s → (⊤ : IntermediateField k L)) = s :=
      Subtype.range_coe
    rw [hr]
    exact hsep
  have : Algebra.FormallySmooth k (⊤ : IntermediateField k L) :=
    .of_algebraicIndependent_of_isSeparable hs.1
  exact Algebra.FormallySmooth.of_equiv IntermediateField.topEquiv

/-- Localization of the base followed by the separably generated field extension. -/
private theorem formallySmooth_fractionRing (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S))
    (hsep : @Algebra.IsSeparableExtension (FractionRing R) (FractionRing S) _ _
      (IsFractionRing.map (K := FractionRing R) (L := FractionRing S) hinj).toAlgebra) :
    Algebra.FormallySmooth R (FractionRing S) := by
  let : Algebra (FractionRing R) (FractionRing S) :=
    (IsFractionRing.map (K := FractionRing R) (L := FractionRing S) hinj).toAlgebra
  have : IsScalarTower R (FractionRing R) (FractionRing S) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext r
    change algebraMap S (FractionRing S) (algebraMap R S r) =
      IsFractionRing.map hinj (algebraMap R (FractionRing R) r)
    exact (IsLocalization.map_eq _ r).symm
  have : Algebra.EssFiniteType S (FractionRing S) :=
    .of_isLocalization _ (nonZeroDivisors S)
  have : Algebra.EssFiniteType R (FractionRing S) := .comp R S _
  have : Algebra.EssFiniteType (FractionRing R) (FractionRing S) := .of_comp R _ _
  have : Algebra.FormallySmooth (FractionRing R) (FractionRing S) :=
    formallySmooth_of_separable_essFiniteType hsep
  have : Algebra.FormallySmooth R (FractionRing R) := .of_isLocalization (nonZeroDivisors R)
  exact .comp R (FractionRing R) _

/-- A smooth neighbourhood in a principal localization descends by clearing denominators. -/
private theorem exists_smooth_localization_of_formallySmooth_fractionRing
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsDomain S] [Algebra R S] (b : S) (hb : b ≠ 0)
    [Algebra.FinitePresentation R (Localization.Away b)]
    [Algebra.FormallySmooth R (FractionRing S)] :
    ∃ g : S, g ≠ 0 ∧ Algebra.Smooth R (Localization.Away g) := by
  let B := Localization.Away b
  have : IsDomain B := Localization.Away.isDomain hb
  let f : B →+* FractionRing S := IsLocalization.Away.lift b
    (show IsUnit (algebraMap S (FractionRing S) b) from
      isUnit_iff_ne_zero.mpr (by
        simpa only [map_zero] using (IsFractionRing.injective S (FractionRing S)).ne hb))
  let : Algebra B (FractionRing S) := f.toAlgebra
  have : IsScalarTower S B (FractionRing S) := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (IsLocalization.Away.lift_comp b _).symm
  have : IsScalarTower R B (FractionRing S) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      change algebraMap S (FractionRing S) (algebraMap R S r) =
        algebraMap B (FractionRing S) (algebraMap S B (algebraMap R S r))
      exact IsScalarTower.algebraMap_apply S B (FractionRing S) _)
  have : IsFractionRing B (FractionRing S) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (.powers b) B _
  have : IsLocalization (⊥ : Ideal B).primeCompl (FractionRing S) := by
    rw [Ideal.primeCompl_bot]
    infer_instance
  let e : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[R] FractionRing S :=
    (IsLocalization.algEquiv (⊥ : Ideal B).primeCompl _ _).restrictScalars R
  have : Algebra.IsSmoothAt R (⊥ : Ideal B) :=
    Algebra.FormallySmooth.of_equiv e.symm
  obtain ⟨a, ha, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R (⊥ : Ideal B)
  have := hsm
  let c := (IsLocalization.Away.sec b a).1
  have hac : Associated (algebraMap S B c) a :=
    IsLocalization.Away.associated_sec_fst b a
  have hc : c ≠ 0 := by
    intro hc
    apply ha
    rw [Ideal.mem_bot]
    exact (hac.eq_zero_iff).mp (by rw [hc, map_zero])
  have : IsLocalization.Away (b * c) (Localization.Away a) :=
    IsLocalization.Away.mul_of_associated b c a hac
  refine ⟨b * c, mul_ne_zero hb hc, ?_⟩
  exact Algebra.Smooth.of_equiv
    ((IsLocalization.algEquiv (.powers (b * c)) (Localization.Away a)
      (Localization.Away (b * c))).restrictScalars R)

/-- If an injective finite type map of integral domains induces a separable extension
of fraction fields, a nonzero principal localization of the target is smooth over the
source. This is the affine ring formulation of generic smoothness.
Source: Stacks Project, Algebra, Lemma 10.42.2 (Tag 07ND).
(blueprint: lem-exc-generic-smooth-domain)

Proof: generic finite presentation supplies a nonzero principal localization `B`
of `S` finitely presented over `R`. Separability and essential finite type make
`Frac(S)` formally smooth over `Frac(R)`, hence over `R` by composition with the
localization `R → Frac(R)`. The zero-prime local ring of `B` is `Frac(S)`.
Mathlib's smooth-locus theorem supplies a smooth principal localization of `B`;
clearing its denominator gives a nonzero smooth principal localization of `S`.
-/
theorem exists_smooth_localization_of_separable_fractionRing
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S))
    (hsep : @IsSeparableExtension (FractionRing R) (FractionRing S) _ _
      (IsFractionRing.map (K := FractionRing R) (L := FractionRing S) hinj).toAlgebra) :
    ∃ g : S, g ≠ 0 ∧ Algebra.Smooth R (Localization.Away g) := by
  have : FormallySmooth R (FractionRing S) :=
    formallySmooth_fractionRing R S hinj hsep
  obtain ⟨a, ha, hfp⟩ := exists_generic_finitePresentation R S
  have hb : algebraMap R S a ≠ 0 := by
    simpa only [map_zero] using hinj.ne ha
  have := hfp
  exact exists_smooth_localization_of_formallySmooth_fractionRing R S (algebraMap R S a) hb

end Algebra
