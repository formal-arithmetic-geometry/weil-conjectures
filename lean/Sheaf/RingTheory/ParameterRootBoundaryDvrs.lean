/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.LinearAlgebra.Basis.Defs

import Sheaf.RingTheory.HenselianParameterRootRegularity
import Sheaf.RingTheory.UniquePrimeLocalization
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.RingTheory.QuotientHenselianPair
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.LocalizationLocalization
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularPrincipalPrimeLocalizationDvr
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Boundary localizations of parameter-root algebras

Source: ILO, Travaux de Gabber, IX Proposition 2.1(i), printed pp.133--134;
Stacks Algebra, Tags 00NQ, 00NP, 04GG, 00PD, 00GK, 00OI.
(blueprint: lem-sfb-parameter-root-boundary-dvrs)

The root algebra is the existing `Algebra.pthRootAlgebra`: its definition allows every
natural root order, without the characteristic restrictions of its locality theorem.
The first theorem states the boundary quotient presentation and its monomial basis.
The second states contraction, DVRs, canonical localization and fraction-field maps,
ramification, and exhaustion of the height-one boundary primes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open scoped TensorProduct
namespace Algebra

/-- The root coordinate in the existing simultaneous root quotient.
Source: ILO IX 2.1(i), p.133 (blueprint: lem-sfb-parameter-root-boundary-dvrs). -/
def parameterRootBoundaryCoordinate {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (i : Fin r) : pthRootAlgebra n r R t :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- The principal parameter ideal in the base ring.
Source: ILO IX 2.1(i), p.133 (blueprint: lem-sfb-parameter-root-boundary-dvrs). -/
def parameterBaseBoundaryIdeal {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (i : Fin r) : Ideal R :=
  Ideal.span {t i}

/-- The principal root ideal in the simultaneous root algebra.
Source: ILO IX 2.1(i), p.133 (blueprint: lem-sfb-parameter-root-boundary-dvrs). -/
def parameterRootBoundaryIdeal {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (i : Fin r) : Ideal (pthRootAlgebra n r R t) :=
  Ideal.span {parameterRootBoundaryCoordinate t n i}

/-- The surviving-variable presentation over the parameter quotient.
Source: ILO IX 2.1(i), p.133, generators and relations after setting one root to zero
(blueprint: lem-sfb-parameter-root-boundary-dvrs). -/
abbrev parameterRootBoundaryPresentation {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (i : Fin r) :=
  MvPolynomial {j : Fin r // j ≠ i} (R ⧸ parameterBaseBoundaryIdeal t i) ⧸
    Ideal.span (Set.range (fun j : {j : Fin r // j ≠ i} ↦
      MvPolynomial.X j ^ n -
        MvPolynomial.C (Ideal.Quotient.mk (parameterBaseBoundaryIdeal t i) (t j.1))))

/-- The canonical coefficient map on boundary quotients, given the ideal containment.
Source: Stacks Algebra, Tag 00CT, applied to ILO IX 2.1(i), p.133
(blueprint: lem-sfb-parameter-root-boundary-dvrs). -/
def parameterRootBoundaryCoefficient {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (i : Fin r)
    (hc : parameterBaseBoundaryIdeal t i ≤
      (parameterRootBoundaryIdeal t n i).comap (algebraMap R (pthRootAlgebra n r R t))) :
    (R ⧸ parameterBaseBoundaryIdeal t i) →+*
      (pthRootAlgebra n r R t ⧸ parameterRootBoundaryIdeal t n i) :=
  Ideal.quotientMap (parameterRootBoundaryIdeal t n i)
    (algebraMap R (pthRootAlgebra n r R t)) hc

set_option backward.isDefEq.respectTransparency true in
private theorem root_regularity
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [HenselianLocalRing R]
    {r : ℕ} (t : Fin r → R) (tail : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail))
    (n : ℕ) (hn : 0 < n) :
    Module.Finite R (pthRootAlgebra n r R t) ∧
      Function.Injective (algebraMap R (pthRootAlgebra n r R t)) ∧
      IsRegularLocalRing (pthRootAlgebra n r R t) := by
  let ts := List.ofFn t ++ tail
  let d := ts.length
  let v : Fin d → R := ts.get
  have hv : List.ofFn v = ts := List.ofFn_get ts
  have hr : r ≤ d := by simp [d, ts]
  have he : v ∘ Fin.castLE hr = t := by
    funext i
    simp [v, ts, List.get_eq_getElem]
  have ht' : IsLocalRing.IsRegularSystemOfParameters (List.ofFn v) := by
    rw [hv]
    exact ht
  obtain ⟨b, hb, hfin, hinj, hint, hreg, hhen, hrest⟩ :=
    henselian_parameter_root_regularity R d v ht' r hr n hn
  rw [he] at hfin hinj hreg
  exact ⟨hfin, hinj, hreg⟩

set_option backward.isDefEq.respectTransparency true in
private theorem regular_parameter_quotient
    {S : Type u} [CommRing S] [IsRegularLocalRing S] (rs : List S)
    (hrs : IsLocalRing.IsRegularSystemOfParameters rs) (x : S) (hx : x ∈ rs) :
    IsRegularLocalRing (S ⧸ Ideal.span {x}) ∧ IsSMulRegular S x := by
  classical
  have hp : rs.Perm (x :: rs.erase x) := List.perm_cons_erase hx
  have hs := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    S rs.length hrs.2.symm rs hrs).2.2 _ hp
  have hq := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    S (x :: rs.erase x).length hs.1.2.symm _ hs.1).2.1 1 (by simp)
  refine ⟨?_, (RingTheory.Sequence.isRegular_cons_iff S x _).mp hs.2 |>.1⟩
  have he : Ideal.ofList ((x :: rs.erase x).take 1) = Ideal.span {x} := by
    simp only [List.take_succ_cons, List.take_zero]
    exact Ideal.ofList_singleton x
  rw [he] at hq
  exact hq.1

set_option backward.isDefEq.respectTransparency true in
private theorem root_parameter_system
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [HenselianLocalRing R]
    {r : ℕ} (t : Fin r → R) (tail : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail))
    (n : ℕ) (hn : 0 < n) :
    ∃ _hreg : IsRegularLocalRing (pthRootAlgebra n r R t),
      IsLocalRing.IsRegularSystemOfParameters
        (List.ofFn (parameterRootBoundaryCoordinate t n) ++
          tail.map (algebraMap R _)) := by
  let ts := List.ofFn t ++ tail
  let d := ts.length
  let v : Fin d → R := ts.get
  have hv : List.ofFn v = ts := List.ofFn_get ts
  have hr : r ≤ d := by simp [d, ts]
  have he : v ∘ Fin.castLE hr = t := by
    funext i
    simp [v, ts, List.get_eq_getElem]
  have ht' : IsLocalRing.IsRegularSystemOfParameters (List.ofFn v) := by
    rw [hv]
    exact ht
  have H := henselian_parameter_root_regularity R d v ht' r hr n hn
  rw [he] at H
  obtain ⟨b, hb, hfin, hinj, hint, hreg, hhen, hrest⟩ := H
  refine ⟨hreg, ?_⟩
  have hp := hrest.2.2.2.1
  have hdrop : (List.ofFn v).drop r = tail := by
    rw [hv]
    change (List.ofFn t ++ tail).drop r = tail
    simp
  rw [hdrop] at hp
  exact hp

set_option backward.isDefEq.respectTransparency true in
private theorem boundary_root_relation
    {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) (n : ℕ) (i : Fin r) :
    parameterRootBoundaryCoordinate t n i ^ n = algebraMap R _ (t i) := by
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span ⟨i, rfl⟩ :
      MvPolynomial.X i ^ n - MvPolynomial.C (t i) ∈
        Ideal.span (Set.range (fun j : Fin r ↦
          (MvPolynomial.X j : MvPolynomial (Fin r) R) ^ n - MvPolynomial.C (t j))))
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk _ (MvPolynomial.X i) ^ n -
    Ideal.Quotient.mk _ (MvPolynomial.C (t i)) = 0
  simpa only [map_sub, map_pow] using hz

set_option backward.isDefEq.respectTransparency true in
private theorem boundary_containment
    {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) (n : ℕ) (hn : 0 < n)
    (i : Fin r) :
    parameterBaseBoundaryIdeal t i ≤
      (parameterRootBoundaryIdeal t n i).comap (algebraMap R _) := by
  apply Ideal.span_le.mpr
  rintro _ rfl
  change algebraMap R _ (t i) ∈ parameterRootBoundaryIdeal t n i
  rw [← boundary_root_relation t n i]
  exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) n hn

set_option backward.isDefEq.respectTransparency true in
private theorem quotient_parameters
    {S : Type u} [CommRing S] [IsRegularLocalRing S] (x : S) (ys : List S)
    (h : IsLocalRing.IsRegularSystemOfParameters (x :: ys)) :
    ∃ _hreg : IsRegularLocalRing (S ⧸ Ideal.span {x}),
      IsLocalRing.IsRegularSystemOfParameters (ys.map (Ideal.Quotient.mk (Ideal.span {x}))) := by
  have hq := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    S (x :: ys).length h.2.symm _ h).2.1 1 (by simp)
  have he : Ideal.ofList ((x :: ys).take 1) = Ideal.span {x} := by
    simp only [List.take_succ_cons, List.take_zero]
    exact Ideal.ofList_singleton x
  rw [he] at hq
  have hreg : IsRegularLocalRing (S ⧸ Ideal.span {x}) := hq.1
  let := hreg
  refine ⟨hreg, ?_, ?_⟩
  · rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective, ← h.1]
    change Ideal.ofList _ = (Ideal.ofList (x :: ys)).map _
    rw [Ideal.ofList_cons, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_ofList]
  · simpa only [List.length_map, List.length_cons, Nat.add_sub_cancel] using hq.2.symm

set_option backward.isDefEq.respectTransparency true in
private theorem quotient_henselian
    {S : Type u} [CommRing S] [HenselianLocalRing S]
    (I : Ideal S) (hI : I ≤ IsLocalRing.maximalIdeal S)
    [IsLocalRing (S ⧸ I)] : HenselianLocalRing (S ⧸ I) := by
  have h := IsLocalRing.henselianRing_quotient_maximalIdeal S I hI
  rw [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
  let := h
  exact { is_henselian := fun f hf a ha hu ↦
    HenselianRing.is_henselian f hf a ha (hu.map _) }

set_option backward.isDefEq.respectTransparency true in
private theorem root_lift
    {R : Type u} [CommRing R] {ι : Type} (t : ι → R) (n : ℕ)
    {S : Type u} [CommRing S] (f : R →+* S) (x : ι → S)
    (hx : ∀ j, x j ^ n = f (t j)) :
    ∃ g : (MvPolynomial ι R ⧸ Ideal.span (Set.range (fun j : ι ↦
        MvPolynomial.X j ^ n - MvPolynomial.C (t j)))) →+* S,
      (∀ a : R, g (Ideal.Quotient.mk _ (MvPolynomial.C a)) = f a) ∧
      ∀ j, g (Ideal.Quotient.mk _ (MvPolynomial.X j)) = x j := by
  let e := MvPolynomial.eval₂Hom f x
  have he : ∀ p ∈ Ideal.span (Set.range (fun j : ι ↦
      MvPolynomial.X j ^ n - MvPolynomial.C (t j))), e p = 0 := by
    change Ideal.span _ ≤ RingHom.ker e
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change e (MvPolynomial.X j ^ n - MvPolynomial.C (t j)) = 0
    simp [e, hx]
  exact ⟨Ideal.Quotient.lift _ e he, fun a ↦ MvPolynomial.eval₂Hom_C f x a,
    fun j ↦ MvPolynomial.eval₂Hom_X' f x j⟩

set_option backward.isDefEq.respectTransparency true in
private theorem root_hom_ext
    {R : Type u} [CommRing R] {ι : Type} (t : ι → R) (n : ℕ)
    {S : Type u} [CommRing S]
    (f g : (MvPolynomial ι R ⧸ Ideal.span (Set.range (fun j : ι ↦
      MvPolynomial.X j ^ n - MvPolynomial.C (t j)))) →+* S)
    (hC : ∀ a, f (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      g (Ideal.Quotient.mk _ (MvPolynomial.C a)))
    (hX : ∀ j, f (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
      g (Ideal.Quotient.mk _ (MvPolynomial.X j))) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · exact hC
  · exact hX

set_option backward.isDefEq.respectTransparency true in
private theorem root_relation
    {R : Type u} [CommRing R] {ι : Type} (t : ι → R) (n : ℕ) (j : ι) :
    (Ideal.Quotient.mk _ (MvPolynomial.X j) :
      MvPolynomial ι R ⧸ Ideal.span (Set.range (fun k : ι ↦
        MvPolynomial.X k ^ n - MvPolynomial.C (t k)))) ^ n =
      Ideal.Quotient.mk _ (MvPolynomial.C (t j)) := by
  apply sub_eq_zero.mp
  rw [← map_pow, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

set_option backward.isDefEq.respectTransparency true in
private theorem boundary_presentation
    {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) (n : ℕ) (hn : 0 < n)
    (i : Fin r) :
    ∃ e : (pthRootAlgebra n r R t ⧸ parameterRootBoundaryIdeal t n i) ≃+*
        parameterRootBoundaryPresentation t n i,
      (∀ a : R, e (Ideal.Quotient.mk _ (algebraMap R _ a)) =
        algebraMap (R ⧸ parameterBaseBoundaryIdeal t i) _ (Ideal.Quotient.mk _ a)) ∧
      ∀ j : {j : Fin r // j ≠ i}, e (Ideal.Quotient.mk _
        (parameterRootBoundaryCoordinate t n j.1)) = Ideal.Quotient.mk _ (MvPolynomial.X j) := by
  classical
  let p := parameterBaseBoundaryIdeal t i
  let q := parameterRootBoundaryIdeal t n i
  let A := R ⧸ p
  let P := parameterRootBoundaryPresentation t n i
  let D := pthRootAlgebra n r R t ⧸ q
  let c : A →+* D := parameterRootBoundaryCoefficient t n i (boundary_containment t n hn i)
  have hc (a : R) : c (Ideal.Quotient.mk p a) =
      Ideal.Quotient.mk q (algebraMap R _ a) := rfl
  let y : Fin r → P := fun j ↦ if h : j = i then 0 else
    Ideal.Quotient.mk _ (MvPolynomial.X (⟨j, h⟩ : {j : Fin r // j ≠ i}))
  have hy (j : Fin r) : y j ^ n = ((algebraMap A P).comp (Ideal.Quotient.mk p)) (t j) := by
    by_cases h : j = i
    · subst j
      simp only [y, dif_pos rfl, zero_pow hn.ne', RingHom.comp_apply]
      have hz : Ideal.Quotient.mk p (t i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [hz, map_zero]
    · simp only [y, dif_neg h, RingHom.comp_apply]
      exact root_relation (fun j : {j : Fin r // j ≠ i} ↦ Ideal.Quotient.mk p (t j.1))
        n ⟨j, h⟩
  obtain ⟨f, hfC, hfX⟩ := root_lift t n ((algebraMap A P).comp (Ideal.Quotient.mk p)) y hy
  have hfq : ∀ b ∈ q, f b = 0 := by
    change q ≤ RingHom.ker f
    apply Ideal.span_le.mpr
    rintro _ rfl
    change f (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0
    rw [hfX]
    simp [y]
  let g : D →+* P := Ideal.Quotient.lift q f hfq
  have hgC (a : R) : g (Ideal.Quotient.mk q (algebraMap R _ a)) =
      algebraMap A P (Ideal.Quotient.mk p a) := hfC a
  have hgX (j : Fin r) : g (Ideal.Quotient.mk q
      (parameterRootBoundaryCoordinate t n j)) = y j := hfX j
  have hz (j : {j : Fin r // j ≠ i}) :
      (Ideal.Quotient.mk q (parameterRootBoundaryCoordinate t n j.1)) ^ n =
        c (Ideal.Quotient.mk p (t j.1)) := by
    rw [hc, ← map_pow, boundary_root_relation]
  obtain ⟨h, hhC, hhX⟩ := root_lift
    (fun j : {j : Fin r // j ≠ i} ↦ Ideal.Quotient.mk p (t j.1)) n c
    (fun j ↦ Ideal.Quotient.mk q (parameterRootBoundaryCoordinate t n j.1)) hz
  have hgh : g.comp h = RingHom.id P := by
    apply root_hom_ext (fun j : {j : Fin r // j ≠ i} ↦ Ideal.Quotient.mk p (t j.1)) n
    · intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      change g (h (Ideal.Quotient.mk _ (MvPolynomial.C (Ideal.Quotient.mk p a)))) = _
      rw [hhC, hc, hgC]
      rfl
    · intro j
      change g (h (Ideal.Quotient.mk _ (MvPolynomial.X j))) = _
      rw [hhX, hgX]
      simp only [y, dif_neg j.property]
      rfl
  have hhg : h.comp g = RingHom.id D := by
    apply Ideal.Quotient.ringHom_ext
    apply root_hom_ext t n
    · intro a
      change h (g (Ideal.Quotient.mk q (algebraMap R _ a))) = _
      rw [hgC]
      exact (hhC (Ideal.Quotient.mk p a)).trans (hc a)
    · intro j
      change h (g (Ideal.Quotient.mk q (parameterRootBoundaryCoordinate t n j))) = _
      by_cases hji : j = i
      · subst j
        have hz : Ideal.Quotient.mk q (parameterRootBoundaryCoordinate t n i) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
        change h (g (Ideal.Quotient.mk q (parameterRootBoundaryCoordinate t n i))) =
          Ideal.Quotient.mk q (parameterRootBoundaryCoordinate t n i)
        rw [hz, map_zero, map_zero]
      · rw [hgX]
        simp only [y, dif_neg hji]
        exact hhX ⟨j, hji⟩
  refine ⟨RingEquiv.ofRingHom g h hgh hhg, hgC, ?_⟩
  intro j
  change g (Ideal.Quotient.mk q (parameterRootBoundaryCoordinate t n j.1)) = _
  rw [hgX]
  simp only [y, dif_neg j.property]

set_option backward.isDefEq.respectTransparency true in
private theorem root_reindex
    {R : Type u} [CommRing R] {k : ℕ} {ι : Type}
    (e : Fin k ≃ ι) (t : ι → R) (n : ℕ) :
    ∃ f : pthRootAlgebra n k R (t ∘ e) ≃ₐ[R]
        (MvPolynomial ι R ⧸ Ideal.span (Set.range (fun j : ι ↦
          MvPolynomial.X j ^ n - MvPolynomial.C (t j)))),
      ∀ j, f (parameterRootCoordinate (t ∘ e) n j) =
        Ideal.Quotient.mk _ (MvPolynomial.X (e j)) := by
  let P := MvPolynomial ι R ⧸ Ideal.span (Set.range (fun j : ι ↦
    MvPolynomial.X j ^ n - MvPolynomial.C (t j)))
  let B := pthRootAlgebra n k R (t ∘ e)
  obtain ⟨f, hfC, hfX⟩ := root_lift (t ∘ e) n (algebraMap R P)
    (fun j ↦ Ideal.Quotient.mk _ (MvPolynomial.X (e j)))
    (fun j ↦ root_relation t n (e j))
  have hfX' (j : Fin k) : f (parameterRootCoordinate (t ∘ e) n j) =
      Ideal.Quotient.mk _ (MvPolynomial.X (e j)) := hfX j
  obtain ⟨g, hgC, hgX⟩ := root_lift t n (algebraMap R B)
    (fun j ↦ parameterRootCoordinate (t ∘ e) n (e.symm j)) (by
      intro j
      change parameterRootBoundaryCoordinate (t ∘ e) n (e.symm j) ^ n = _
      rw [boundary_root_relation]
      simp only [Function.comp_apply, e.apply_symm_apply]
      rfl)
  have hfg : f.comp g = RingHom.id P := by
    apply root_hom_ext t n
    · intro a
      change f (g (Ideal.Quotient.mk _ (MvPolynomial.C a))) = _
      rw [hgC]
      exact hfC a
    · intro j
      change f (g (Ideal.Quotient.mk _ (MvPolynomial.X j))) = _
      rw [hgX, hfX', e.apply_symm_apply]
      rfl
  have hgf : g.comp f = RingHom.id B := by
    apply root_hom_ext (t ∘ e) n
    · intro a
      change g (f (Ideal.Quotient.mk _ (MvPolynomial.C a))) = _
      rw [hfC]
      exact hgC a
    · intro j
      change g (f (parameterRootCoordinate (t ∘ e) n j)) = _
      rw [hfX', hgX, e.symm_apply_apply]
      rfl
  refine ⟨{ __ := RingEquiv.ofRingHom f g hfg hgf, commutes' := hfC }, hfX⟩

set_option backward.isDefEq.respectTransparency false in
private theorem parameter_survivors
    {R : Type u} [CommRing R] [IsRegularLocalRing R] {k : ℕ}
    (t : Fin (k + 1) → R) (tail : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail))
    (i : Fin (k + 1)) :
    ∃ _hreg : IsRegularLocalRing (R ⧸ parameterBaseBoundaryIdeal t i),
      IsLocalRing.IsRegularSystemOfParameters
        (List.ofFn (fun j : Fin k ↦ Ideal.Quotient.mk (parameterBaseBoundaryIdeal t i)
          (t (i.succAbove j))) ++
          tail.map (Ideal.Quotient.mk (parameterBaseBoundaryIdeal t i))) := by
  let σ : Equiv.Perm (Fin (k + 1)) := (finSuccEquiv k).trans (finSuccEquiv' i).symm
  have hzero : σ 0 = i := by simp [σ]
  have hsucc (j : Fin k) : σ j.succ = i.succAbove j := by simp [σ]
  have hp : (t i :: List.ofFn (t ∘ i.succAbove)).Perm (List.ofFn t) := by
    have h := σ.ofFn_comp_perm t
    rw [List.ofFn_succ] at h
    simpa only [Function.comp_def, hzero, hsucc] using h
  have hs := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    R (List.ofFn t ++ tail).length ht.2.symm _ ht).2.2 _ (hp.append_right tail).symm
  obtain ⟨hreg, hparams⟩ := quotient_parameters (t i) (List.ofFn (t ∘ i.succAbove) ++ tail) hs.1
  refine ⟨hreg, ?_⟩
  simpa only [List.map_append, List.map_ofFn, Function.comp_def,
    parameterBaseBoundaryIdeal] using hparams

set_option backward.isDefEq.respectTransparency true in
private theorem partial_root_basis
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [HenselianLocalRing R]
    {r : ℕ} (t : Fin r → R) (tail : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail))
    (n : ℕ) (hn : 0 < n) :
    ∃ b : Module.Basis (Fin r → Fin n) R (pthRootAlgebra n r R t),
      ∀ a, b a = ∏ j, parameterRootCoordinate t n j ^ (a j).val := by
  let ts := List.ofFn t ++ tail
  let d := ts.length
  let v : Fin d → R := ts.get
  have hv : List.ofFn v = ts := List.ofFn_get ts
  have hr : r ≤ d := by simp [d, ts]
  have he : v ∘ Fin.castLE hr = t := by
    funext i
    simp [v, ts, List.get_eq_getElem]
  have ht' : IsLocalRing.IsRegularSystemOfParameters (List.ofFn v) := by
    rw [hv]
    exact ht
  have H := henselian_parameter_root_regularity R d v ht' r hr n hn
  rw [he] at H
  obtain ⟨b, hb, _⟩ := H
  exact ⟨b, hb⟩

set_option backward.isDefEq.respectTransparency true in
/-- Boundary quotients are regular local domains and have the canonical surviving-root
presentation and its finite monomial basis, including the constant monomial.
Source: ILO IX Proposition 2.1(i), pp.133--134; Stacks Tags 00NQ, 00NP, 04GG.
(blueprint: lem-sfb-parameter-root-boundary-dvrs)

Proof (steps 1--4 of the node): apply henselian-parameter-root-regularity to get the
regular local domain root algebra and its full parameter system. Permute parameters
so that the selected parameter comes first. Regular-local-generators-regular-sequence
makes it a nonzerodivisor and its quotient regular local; regular-local-domain makes
both quotients domains. Set the selected root to zero in the presentation. Its root
relation forces the corresponding parameter to vanish since n > 0. Sending the
remaining variables to their classes and coefficients to their residue classes gives
inverse maps on generators. The base quotient is henselian, and its surviving
parameters form a regular system. Apply henselian-parameter-root-regularity over
that quotient and transport its monomial basis along the presentation and the
finite-index equivalence. The resulting nonempty finite basis makes the coefficient
map injective and finite. -/
theorem parameter_root_boundary_quotients
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [HenselianLocalRing R]
    {r : ℕ} (t : Fin r → R) (tail : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail))
    (n : ℕ) (hn : 0 < n) (i : Fin r) :
    IsRegularLocalRing (R ⧸ parameterBaseBoundaryIdeal t i) ∧
    IsDomain (R ⧸ parameterBaseBoundaryIdeal t i) ∧
    IsRegularLocalRing (pthRootAlgebra n r R t ⧸ parameterRootBoundaryIdeal t n i) ∧
    IsDomain (pthRootAlgebra n r R t ⧸ parameterRootBoundaryIdeal t n i) ∧
    IsSMulRegular R (t i) ∧
    IsSMulRegular (pthRootAlgebra n r R t) (parameterRootBoundaryCoordinate t n i) ∧
    ∃ hc : parameterBaseBoundaryIdeal t i ≤
        (parameterRootBoundaryIdeal t n i).comap (algebraMap R (pthRootAlgebra n r R t)),
      Function.Injective (parameterRootBoundaryCoefficient t n i hc) ∧
      (parameterRootBoundaryCoefficient t n i hc).Finite ∧
      (∃ b : @Module.Basis ({j : Fin r // j ≠ i} → Fin n)
          (R ⧸ parameterBaseBoundaryIdeal t i)
          (pthRootAlgebra n r R t ⧸ parameterRootBoundaryIdeal t n i) _ _
          (parameterRootBoundaryCoefficient t n i hc).toAlgebra.toModule,
        ∀ a, b a = ∏ j : {j : Fin r // j ≠ i},
          Ideal.Quotient.mk (parameterRootBoundaryIdeal t n i)
            (parameterRootBoundaryCoordinate t n j.1) ^ (a j).val) ∧
      ∃ e : (pthRootAlgebra n r R t ⧸ parameterRootBoundaryIdeal t n i) ≃+*
          parameterRootBoundaryPresentation t n i,
        (∀ a : R,
          e (Ideal.Quotient.mk (parameterRootBoundaryIdeal t n i)
            (algebraMap R (pthRootAlgebra n r R t) a)) =
          algebraMap (R ⧸ parameterBaseBoundaryIdeal t i)
            (parameterRootBoundaryPresentation t n i)
            (Ideal.Quotient.mk (parameterBaseBoundaryIdeal t i) a)) ∧
        ∀ j : {j : Fin r // j ≠ i},
          e (Ideal.Quotient.mk (parameterRootBoundaryIdeal t n i)
            (parameterRootBoundaryCoordinate t n j.1)) =
          Ideal.Quotient.mk _ (MvPolynomial.X j) := by
  classical
  cases r with
  | zero => exact Fin.elim0 i
  | succ k =>
    obtain ⟨hR, htr⟩ := regular_parameter_quotient (List.ofFn t ++ tail) ht (t i)
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
    obtain ⟨hB, hparams⟩ := root_parameter_system t tail ht n hn
    let := hB
    obtain ⟨hD, hxr⟩ := regular_parameter_quotient
      (List.ofFn (parameterRootBoundaryCoordinate t n) ++ tail.map (algebraMap R _))
      hparams (parameterRootBoundaryCoordinate t n i)
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
    have hA : IsRegularLocalRing (R ⧸ parameterBaseBoundaryIdeal t i) := hR
    let := hA
    have hD' : IsRegularLocalRing
        (pthRootAlgebra n (k + 1) R t ⧸ parameterRootBoundaryIdeal t n i) := hD
    let := hD'
    refine ⟨hA, inferInstance, hD', inferInstance, htr, hxr, ?_⟩
    let p := parameterBaseBoundaryIdeal t i
    let q := parameterRootBoundaryIdeal t n i
    let A := R ⧸ p
    let D := pthRootAlgebra n (k + 1) R t ⧸ q
    let P := parameterRootBoundaryPresentation t n i
    let hc := boundary_containment t n hn i
    let c : A →+* D := parameterRootBoundaryCoefficient t n i hc
    let : Algebra A D := c.toAlgebra
    obtain ⟨e, heC, heX⟩ := boundary_presentation t n hn i
    let ea : D ≃ₐ[A] P := {
      __ := e
      commutes' := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact heC a }
    have hp : p ≤ IsLocalRing.maximalIdeal R := by
      apply Ideal.span_le.mpr
      rintro _ rfl
      rw [← ht.1]
      exact Ideal.subset_span (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
    have : HenselianLocalRing A := quotient_henselian p hp
    obtain ⟨_, hs⟩ := parameter_survivors t tail ht i
    let v : Fin k → A := fun j ↦ Ideal.Quotient.mk p (t (i.succAbove j))
    obtain ⟨b, hb⟩ := partial_root_basis v (tail.map (Ideal.Quotient.mk p)) hs n hn
    let ei := finSuccAboveEquiv i
    obtain ⟨f, hfX⟩ := root_reindex ei
      (fun j : {j : Fin (k + 1) // j ≠ i} ↦ Ideal.Quotient.mk p (t j.1)) n
    let ee : (Fin k → Fin n) ≃ ({j : Fin (k + 1) // j ≠ i} → Fin n) := {
      toFun := fun a j ↦ a (ei.symm j)
      invFun := fun a j ↦ a (ei j)
      left_inv := by intro a; funext j; simp
      right_inv := by intro a; funext j; simp }
    let g : pthRootAlgebra n k A v ≃ₐ[A] D := f.trans ea.symm
    let bd := (b.map g.toLinearEquiv).reindex ee
    have hbd (a : {j : Fin (k + 1) // j ≠ i} → Fin n) :
        bd a = ∏ j, Ideal.Quotient.mk q (parameterRootBoundaryCoordinate t n j.1) ^
          (a j).val := by
      rw [Module.Basis.reindex_apply, Module.Basis.map_apply, hb]
      change g (∏ j, parameterRootCoordinate v n j ^ ((ee.symm a) j).val) = _
      rw [map_prod]
      apply Fintype.prod_equiv ei
      intro j
      rw [map_pow]
      congr 1
      change ea.symm (f (parameterRootCoordinate
        ((fun j : {j : Fin (k + 1) // j ≠ i} ↦
          Ideal.Quotient.mk p (t j.1)) ∘ ei) n j)) = _
      rw [hfX]
      apply ea.injective
      rw [ea.apply_symm_apply]
      exact (heX (ei j)).symm
    have : Module.Free A D := Module.Free.of_basis bd
    have : Module.Finite A D := Module.Finite.of_basis bd
    have hinj : Function.Injective c := FaithfulSMul.algebraMap_injective A D
    have hfin : c.Finite := RingHom.finite_algebraMap.mpr inferInstance
    exact ⟨hc, hinj, hfin, ⟨bd, hbd⟩, e, heC, heX⟩


set_option backward.isDefEq.respectTransparency true in
private theorem boundary_contraction
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [HenselianLocalRing R]
    {r : ℕ} (t : Fin r → R) (tail : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail))
    (n : ℕ) (hn : 0 < n) (i : Fin r) :
    (parameterBaseBoundaryIdeal t i).IsPrime ∧
      (parameterRootBoundaryIdeal t n i).IsPrime ∧
      parameterBaseBoundaryIdeal t i =
        (parameterRootBoundaryIdeal t n i).comap (algebraMap R _) := by
  obtain ⟨hR, hRD, hB, hBD, htr, hxr, hc, hinj, hrest⟩ :=
    parameter_root_boundary_quotients t tail ht n hn i
  let := hRD
  let := hBD
  refine ⟨(Ideal.Quotient.isDomain_iff_prime _).mp inferInstance,
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance, le_antisymm hc ?_⟩
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hinj
  change Ideal.Quotient.mk (parameterRootBoundaryIdeal t n i)
    (algebraMap R _ a) = parameterRootBoundaryCoefficient t n i hc 0
  rw [map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

set_option backward.isDefEq.respectTransparency true in
private theorem boundary_height
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [HenselianLocalRing R]
    {r : ℕ} (t : Fin r → R) (tail : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail))
    (n : ℕ) (hn : 0 < n) (i : Fin r) :
    (parameterRootBoundaryIdeal t n i).height = 1 := by
  let := (root_regularity t tail ht n hn).2.2
  obtain ⟨_, _, _, hBD, _, hx, _⟩ :=
    parameter_root_boundary_quotients t tail ht n hn i
  let := hBD
  have hp : (parameterRootBoundaryIdeal t n i).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hBD
  apply Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr (fun hzero ↦ by
      have heq : (1 : pthRootAlgebra n r R t) = 0 := hx (by simp [hzero])
      exact one_ne_zero heq)
  · intro hu
    exact hp.ne_top (Ideal.span_singleton_eq_top.mpr hu)

set_option backward.isDefEq.respectTransparency true in
private theorem boundary_unique_prime
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [HenselianLocalRing R]
    {r : ℕ} (t : Fin r → R) (tail : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail))
    (n : ℕ) (hn : 0 < n) (i : Fin r)
    (Q : Ideal (pthRootAlgebra n r R t)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap R _) = parameterBaseBoundaryIdeal t i) :
    Q = parameterRootBoundaryIdeal t n i := by
  let := (root_regularity t tail ht n hn).1
  obtain ⟨_, hq, hc⟩ := boundary_contraction t tail ht n hn i
  let := hq
  have hle : parameterRootBoundaryIdeal t n i ≤ Q := by
    apply Ideal.span_le.mpr
    rintro _ rfl
    apply (Ideal.IsPrime.pow_mem_iff_mem (inferInstance : Q.IsPrime) n hn).mp
    rw [boundary_root_relation]
    change t i ∈ Q.comap (algebraMap R _)
    rw [hQ]
    exact Ideal.subset_span (by simp)
  apply Eq.symm
  apply eq_of_le_of_not_lt hle
  intro hlt
  have hh := Ideal.IsIntegral.comap_lt_comap (R := R) hlt
  rw [hQ, ← hc] at hh
  exact lt_irrefl _ hh

set_option backward.isDefEq.respectTransparency true in
private theorem boundary_local_comparison
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [HenselianLocalRing R]
    {r : ℕ} (t : Fin r → R) (tail : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail))
    (n : ℕ) (hn : 0 < n) (i : Fin r)
    [hp : (parameterBaseBoundaryIdeal t i).IsPrime]
    [hq : (parameterRootBoundaryIdeal t n i).IsPrime]
    (hc : parameterBaseBoundaryIdeal t i =
      (parameterRootBoundaryIdeal t n i).comap (algebraMap R _)) :
    ∃ e : (pthRootAlgebra n r R t ⊗[R]
        Localization.AtPrime (parameterBaseBoundaryIdeal t i)) ≃+*
        Localization.AtPrime (parameterRootBoundaryIdeal t n i),
      (∀ b, e (b ⊗ₜ[R] (1 : Localization.AtPrime (parameterBaseBoundaryIdeal t i))) =
        algebraMap _ _ b) ∧
      (∀ v, e ((1 : pthRootAlgebra n r R t) ⊗ₜ[R] v) =
        Localization.localRingHom _ _ (algebraMap R _) hc v) ∧
      (Localization.localRingHom _ _ (algebraMap R _) hc).Finite := by
  let := (root_regularity t tail ht n hn).1
  let p := parameterBaseBoundaryIdeal t i
  let q := parameterRootBoundaryIdeal t n i
  let B := pthRootAlgebra n r R t
  have hu := (IsLocalization.uniquePrimeLocalization.{u, u, u} p q hc.symm
    (fun Q hQ hcon ↦ by
      let := hQ
      exact boundary_unique_prime t tail ht n hn i Q hcon)).1
  let e := (Localization.tensorLeftAlgEquiv p.primeCompl B).trans
    (AlgEquiv.ofBijective (IsLocalization.uniquePrimeLocalizationMap p q hc.symm) hu)
  have heb (b : B) : e (b ⊗ₜ[R] (1 : Localization.AtPrime p)) = algebraMap B _ b :=
    e.commutes b
  have hev : e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      Localization.localRingHom p q (algebraMap R B) hc := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    change e ((1 : B) ⊗ₜ[R] algebraMap R (Localization.AtPrime p) a) = _
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_one, heb, RingHom.comp_apply,
      Localization.localRingHom_to_map]
  refine ⟨e.toRingEquiv, heb, fun v ↦ DFunLike.congr_fun hev v, ?_⟩
  rw [← hev]
  apply e.toRingEquiv.finite.comp
  have hf : (algebraMap (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] B)).Finite :=
    RingHom.finite_algebraMap.mpr inferInstance
  have he := (Algebra.TensorProduct.comm R (Localization.AtPrime p) B).toRingEquiv.finite
  convert he.comp hf using 1
  ext v
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem boundary_fraction_fields
    {R B : Type u} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra R B] (hRB : Function.Injective (algebraMap R B))
    (p : Ideal R) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hc : p = q.comap (algebraMap R B))
    (hj : Function.Injective (Localization.localRingHom p q (algebraMap R B) hc)) :
    ∃ (ev : FractionRing (Localization.AtPrime p) ≃+* FractionRing R)
      (ea : FractionRing (Localization.AtPrime q) ≃+* FractionRing B),
      (∀ a : R, ev (algebraMap (Localization.AtPrime p) _ (algebraMap R _ a)) =
        algebraMap R (FractionRing R) a) ∧
      (∀ b : B, ea (algebraMap (Localization.AtPrime q) _ (algebraMap B _ b)) =
        algebraMap B (FractionRing B) b) ∧
      ea.toRingHom.comp (IsFractionRing.map hj) =
        (IsFractionRing.map (K := FractionRing R) (L := FractionRing B) hRB).comp
          ev.toRingHom := by
  let ev := (IsLocalization.algEquiv (nonZeroDivisors (Localization.AtPrime p))
    (FractionRing (Localization.AtPrime p)) (FractionRing R)).toRingEquiv
  let ea := (IsLocalization.algEquiv (nonZeroDivisors (Localization.AtPrime q))
    (FractionRing (Localization.AtPrime q)) (FractionRing B)).toRingEquiv
  have hev (a : R) : ev (algebraMap (Localization.AtPrime p) _ (algebraMap R _ a)) =
      algebraMap R (FractionRing R) a := by
    rw [show ev (algebraMap (Localization.AtPrime p) _ (algebraMap R _ a)) =
      algebraMap (Localization.AtPrime p) (FractionRing R) (algebraMap R _ a) from
        (IsLocalization.algEquiv (nonZeroDivisors (Localization.AtPrime p))
          (FractionRing (Localization.AtPrime p)) (FractionRing R)).commutes _]
    exact (IsScalarTower.algebraMap_apply R (Localization.AtPrime p) (FractionRing R) a).symm
  have hea (b : B) : ea (algebraMap (Localization.AtPrime q) _ (algebraMap B _ b)) =
      algebraMap B (FractionRing B) b := by
    rw [show ea (algebraMap (Localization.AtPrime q) _ (algebraMap B _ b)) =
      algebraMap (Localization.AtPrime q) (FractionRing B) (algebraMap B _ b) from
        (IsLocalization.algEquiv (nonZeroDivisors (Localization.AtPrime q))
          (FractionRing (Localization.AtPrime q)) (FractionRing B)).commutes _]
    exact (IsScalarTower.algebraMap_apply B (Localization.AtPrime q) (FractionRing B) b).symm
  refine ⟨ev, ea, hev, hea, ?_⟩
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Localization.AtPrime p))
  apply IsLocalization.ringHom_ext p.primeCompl
  ext a
  simp only [RingHom.comp_apply, IsFractionRing.map, IsLocalization.map_eq,
    Localization.localRingHom_to_map]
  change ea (algebraMap (Localization.AtPrime q) _ (algebraMap B _ (algebraMap R B a))) =
    IsFractionRing.map hRB
      (ev (algebraMap (Localization.AtPrime p) _ (algebraMap R _ a)))
  rw [hea, hev]
  exact (IsLocalization.map_eq _ a).symm

set_option backward.isDefEq.respectTransparency true in
/-- Boundary prime localizations are DVRs with the canonical finite localization
comparison, induced fraction-field map and ramification ideal equality. These are
exactly the height-one primes containing the boundary product, also for an empty boundary.
Source: ILO IX Proposition 2.1(i), pp.133--134; Stacks Tags 00PD, 00GK, 00OI, 00E3.
(blueprint: lem-sfb-parameter-root-boundary-dvrs)

Proof: root regularity gives a domain and an injective finite coefficient map.
The quotient theorem gives prime boundary ideals and their contraction, and the
regular-principal-prime-localization-DVR criterion gives both DVRs. Any prime over
(t_i) contains x_i by the root relation; integral incomparability then makes it
(x_i). The unique-prime-localization theorem identifies the base localization of B
with B_(x_i). The tensor-localization comparison gives the stated canonical map,
and finite base change proves finiteness. Injectivity follows from localization of
the original domain injection. Fraction fields are invariant under localization;
extensionality on the original coefficients proves the commuting square. The root
relation and powers of principal ideals give the ramification equality. The nonzero
principal prime (x_i) has height one by the principal ideal theorem. Finally, a
prime containing the boundary product contains one root, and equality of heights
forces equality with its root ideal. For an empty boundary, no prime contains 1. -/
theorem parameter_root_boundary_dvrs
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [HenselianLocalRing R]
    {r : ℕ} (t : Fin r → R) (tail : List R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ tail))
    (n : ℕ) (hn : 0 < n) :
    ∃ (_ : IsDomain (pthRootAlgebra n r R t)),
    ∃ hRB : Function.Injective (algebraMap R (pthRootAlgebra n r R t)),
      (∀ Q : Ideal (pthRootAlgebra n r R t), Q.IsPrime →
        (Q.height = 1 ∧ algebraMap R (pthRootAlgebra n r R t) (∏ j, t j) ∈ Q ↔
          ∃ i : Fin r, Q = parameterRootBoundaryIdeal t n i)) ∧
      ∀ i : Fin r,
        ∃ (_ : (parameterBaseBoundaryIdeal t i).IsPrime),
        ∃ (_ : (parameterRootBoundaryIdeal t n i).IsPrime),
        ∃ hc : parameterBaseBoundaryIdeal t i =
            (parameterRootBoundaryIdeal t n i).comap (algebraMap R (pthRootAlgebra n r R t)),
        ∃ (_ : IsDiscreteValuationRing (Localization.AtPrime (parameterBaseBoundaryIdeal t i))),
        ∃ (_ : IsDiscreteValuationRing
            (Localization.AtPrime (parameterRootBoundaryIdeal t n i))),
          (parameterRootBoundaryIdeal t n i).height = 1 ∧
          IsLocalRing.maximalIdeal (Localization.AtPrime (parameterBaseBoundaryIdeal t i)) =
            Ideal.span {algebraMap R (Localization.AtPrime (parameterBaseBoundaryIdeal t i))
              (t i)} ∧
          IsLocalRing.maximalIdeal (Localization.AtPrime (parameterRootBoundaryIdeal t n i)) =
            Ideal.span {algebraMap (pthRootAlgebra n r R t)
              (Localization.AtPrime (parameterRootBoundaryIdeal t n i))
              (parameterRootBoundaryCoordinate t n i)} ∧
          (∃ e : (pthRootAlgebra n r R t ⊗[R]
              Localization.AtPrime (parameterBaseBoundaryIdeal t i)) ≃+*
              Localization.AtPrime (parameterRootBoundaryIdeal t n i),
            (∀ b : pthRootAlgebra n r R t,
              e (b ⊗ₜ[R] (1 : Localization.AtPrime (parameterBaseBoundaryIdeal t i))) =
                algebraMap (pthRootAlgebra n r R t) _ b) ∧
            ∀ v : Localization.AtPrime (parameterBaseBoundaryIdeal t i),
              e ((1 : pthRootAlgebra n r R t) ⊗ₜ[R] v) =
                Localization.localRingHom (parameterBaseBoundaryIdeal t i)
                  (parameterRootBoundaryIdeal t n i)
                  (algebraMap R (pthRootAlgebra n r R t)) hc v) ∧
          ∃ hj : Function.Injective
              (Localization.localRingHom (parameterBaseBoundaryIdeal t i)
                (parameterRootBoundaryIdeal t n i) (algebraMap R (pthRootAlgebra n r R t)) hc),
            (Localization.localRingHom (parameterBaseBoundaryIdeal t i)
              (parameterRootBoundaryIdeal t n i)
              (algebraMap R (pthRootAlgebra n r R t)) hc).Finite ∧
            (∃ (ev : FractionRing (Localization.AtPrime (parameterBaseBoundaryIdeal t i)) ≃+*
                FractionRing R)
              (ea : FractionRing (Localization.AtPrime (parameterRootBoundaryIdeal t n i)) ≃+*
                FractionRing (pthRootAlgebra n r R t)),
              (∀ a : R,
                ev (algebraMap (Localization.AtPrime (parameterBaseBoundaryIdeal t i)) _
                  (algebraMap R _ a)) = algebraMap R (FractionRing R) a) ∧
              (∀ b : pthRootAlgebra n r R t,
                ea (algebraMap (Localization.AtPrime (parameterRootBoundaryIdeal t n i)) _
                  (algebraMap (pthRootAlgebra n r R t) _ b)) =
                  algebraMap (pthRootAlgebra n r R t) (FractionRing (pthRootAlgebra n r R t)) b) ∧
              ea.toRingHom.comp (IsFractionRing.map hj) =
                (IsFractionRing.map (K := FractionRing R)
                  (L := FractionRing (pthRootAlgebra n r R t)) hRB).comp ev.toRingHom) ∧
            Ideal.map (Localization.localRingHom (parameterBaseBoundaryIdeal t i)
                (parameterRootBoundaryIdeal t n i) (algebraMap R (pthRootAlgebra n r R t)) hc)
                (IsLocalRing.maximalIdeal
                  (Localization.AtPrime (parameterBaseBoundaryIdeal t i))) =
              Ideal.span {algebraMap R
                (Localization.AtPrime (parameterRootBoundaryIdeal t n i)) (t i)} ∧
            Ideal.span {algebraMap R
                (Localization.AtPrime (parameterRootBoundaryIdeal t n i)) (t i)} =
              Ideal.span {(algebraMap (pthRootAlgebra n r R t)
                (Localization.AtPrime (parameterRootBoundaryIdeal t n i))
                (parameterRootBoundaryCoordinate t n i)) ^ n} ∧
            Ideal.span {(algebraMap (pthRootAlgebra n r R t)
                (Localization.AtPrime (parameterRootBoundaryIdeal t n i))
                (parameterRootBoundaryCoordinate t n i)) ^ n} =
              IsLocalRing.maximalIdeal
                (Localization.AtPrime (parameterRootBoundaryIdeal t n i)) ^ n := by
  classical
  obtain ⟨hfin, hRB, hreg⟩ := root_regularity t tail ht n hn
  let := hfin
  let := hreg
  refine ⟨inferInstance, hRB, ?_, ?_⟩
  · intro Q hQ
    let := hQ
    constructor
    · rintro ⟨hheight, hprod⟩
      rw [map_prod] at hprod
      obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
      have hxi : parameterRootBoundaryCoordinate t n i ∈ Q := by
        apply (hQ.pow_mem_iff_mem n hn).mp
        rwa [boundary_root_relation]
      have hle : parameterRootBoundaryIdeal t n i ≤ Q :=
        Ideal.span_le.mpr (by rintro _ rfl; exact hxi)
      have hp := (boundary_contraction t tail ht n hn i).2.1
      let := hp
      refine ⟨i, ?_⟩
      exact (Ideal.eq_of_le_of_height_le _ hle (by
        rw [hheight, boundary_height t tail ht n hn i])).symm
    · rintro ⟨i, rfl⟩
      refine ⟨boundary_height t tail ht n hn i, ?_⟩
      rw [map_prod]
      apply Ideal.IsPrime.prod_mem_iff.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [← boundary_root_relation t n i]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self
        (parameterRootBoundaryCoordinate t n i)) n hn
  · intro i
    obtain ⟨hp, hq, hc⟩ := boundary_contraction t tail ht n hn i
    let := hp
    let := hq
    obtain ⟨_, _, _, _, htr, hxr, _⟩ :=
      parameter_root_boundary_quotients t tail ht n hn i
    have : (Ideal.span {t i}).IsPrime := hp
    have : (Ideal.span {parameterRootBoundaryCoordinate t n i}).IsPrime := hq
    have : IsLocalization.AtPrime
        (Localization.AtPrime (parameterBaseBoundaryIdeal t i)) (Ideal.span {t i}) := by
      delta parameterBaseBoundaryIdeal
      infer_instance
    have : IsLocalization.AtPrime
        (Localization.AtPrime (parameterRootBoundaryIdeal t n i))
        (Ideal.span {parameterRootBoundaryCoordinate t n i}) := by
      delta parameterRootBoundaryIdeal
      infer_instance
    obtain ⟨hV, hVD, _⟩ := IsLocalization.regular_principal_prime_dvr
      (B := Localization.AtPrime (parameterBaseBoundaryIdeal t i)) (t i) htr
    obtain ⟨hA, hAD, _⟩ := IsLocalization.regular_principal_prime_dvr
      (B := Localization.AtPrime (parameterRootBoundaryIdeal t n i))
      (parameterRootBoundaryCoordinate t n i) hxr
    let := hV
    let := hA
    let := hVD
    let := hAD
    have hmV : IsLocalRing.maximalIdeal
        (Localization.AtPrime (parameterBaseBoundaryIdeal t i)) =
        Ideal.span {algebraMap R _ (t i)} := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parameterBaseBoundaryIdeal t i)]
      change (Ideal.span {t i}).map _ = _
      rw [Ideal.map_span, Set.image_singleton]
    have hmA : IsLocalRing.maximalIdeal
        (Localization.AtPrime (parameterRootBoundaryIdeal t n i)) =
        Ideal.span {algebraMap (pthRootAlgebra n r R t) _
          (parameterRootBoundaryCoordinate t n i)} := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parameterRootBoundaryIdeal t n i)]
      change (Ideal.span {parameterRootBoundaryCoordinate t n i}).map _ = _
      rw [Ideal.map_span, Set.image_singleton]
    obtain ⟨e, heb, hev, hf⟩ := boundary_local_comparison t tail ht n hn i hc
    have hj : Function.Injective (Localization.localRingHom _ _ (algebraMap R _) hc) := by
      exact IsLocalization.map_injective_of_injective'
        (S := pthRootAlgebra n r R t)
        (M := (parameterBaseBoundaryIdeal t i).primeCompl)
        (Sₘ := Localization.AtPrime (parameterRootBoundaryIdeal t n i))
        (hf := fun a ha ↦ by
          change a ∉ (parameterBaseBoundaryIdeal t i) at ha
          rw [hc] at ha
          exact ha)
        (hN := fun h ↦ h (Ideal.zero_mem _)) (hf' := hRB)
    refine ⟨hp, hq, hc, hVD, hAD, boundary_height t tail ht n hn i, hmV, hmA,
      ⟨e, heb, hev⟩, hj, hf, boundary_fraction_fields hRB _ _ hc hj, ?_, ?_, ?_⟩
    · rw [hmV, Ideal.map_span, Set.image_singleton, Localization.localRingHom_to_map]
      rfl
    · rw [IsScalarTower.algebraMap_apply R (pthRootAlgebra n r R t),
        ← boundary_root_relation t n i, map_pow]
    · rw [hmA, Ideal.span_singleton_pow]


end Algebra
