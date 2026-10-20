/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Regular.Flat
import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood
import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-! # Lifting a specified fibre regular sequence

Source: Stacks Project, Divisors, Tag 063W, proof of assertion (1).
(blueprint: lem-pur-fiber-regular-sequence-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u

open scoped TensorProduct

namespace Algebra

private local instance tensorAddCommGroup (R A B : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] : AddCommGroup (A ⊗[R] B) :=
  (inferInstance : CommRing (A ⊗[R] B)).toAddCommGroup

private lemma weak_cons_quotient_iff
    {A : Type u} [CommRing A] (f : A) (fs : List A) :
    RingTheory.Sequence.IsWeaklyRegular A (f :: fs) ↔
      IsSMulRegular A f ∧ RingTheory.Sequence.IsWeaklyRegular (A ⧸ Ideal.span {f})
        (fs.map (Ideal.Quotient.mk (Ideal.span {f}))) := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
  apply and_congr_right'
  let e : QuotSMulTop f A ≃ₗ[A] A ⧸ Ideal.span {f} :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
  exact (e.isWeaklyRegular_congr fs).trans
    (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff _ _ fs).symm

private lemma weak_map_equiv
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) (fs : List A)
    (h : RingTheory.Sequence.IsWeaklyRegular A fs) :
    RingTheory.Sequence.IsWeaklyRegular B (fs.map e) := by
  exact (e.toAddEquiv.isWeaklyRegular_congr
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun x _ y ↦ e.map_mul x y)))).mp h

set_option backward.isDefEq.respectTransparency false in
private lemma weak_fiber_quotient
    (R A K : Type u) [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] (f : A) (fs : List A)
    (h : RingTheory.Sequence.IsWeaklyRegular (K ⊗[R] A)
      ((f :: fs).map (TensorProduct.includeRight (R := R) (A := K)).toRingHom)) :
    RingTheory.Sequence.IsWeaklyRegular (K ⊗[R] (A ⧸ Ideal.span {f}))
      ((fs.map (Ideal.Quotient.mk (Ideal.span {f}))).map
        (TensorProduct.includeRight (R := R) (A := K)).toRingHom) := by
  let F := K ⊗[R] A
  let J : Ideal A := Ideal.span {f}
  let e := TensorProduct.tensorQuotientEquiv (R := R) K A K J
  have hJ : J.map (TensorProduct.includeRight (R := R) (A := K)) =
      Ideal.span {((TensorProduct.includeRight (R := R) (A := K) f) : F)} := by
    rw [Ideal.map_span, Set.image_singleton]
  have ht := ((weak_cons_quotient_iff ((TensorProduct.includeRight (R := R) (A := K) f))
    (fs.map (TensorProduct.includeRight (R := R) (A := K)).toRingHom)).mp h).2
  rw [← hJ] at ht
  have hw := weak_map_equiv e.symm.toRingEquiv _ ht
  have he (a : A) : e.symm.toRingEquiv
      (Ideal.Quotient.mk _ ((TensorProduct.includeRight (R := R) (A := K)).toRingHom a)) =
      TensorProduct.includeRight (Ideal.Quotient.mk J a) := rfl
  dsimp only [J] at hw he
  convert hw using 1
  · with_reducible_and_instances rfl
  · simp only [List.map_map, Function.comp_def, he]
    rfl

set_option backward.isDefEq.respectTransparency false in
private lemma weak_fiber_localization
    (R A K B : Type u) [CommRing R] [CommRing A] [CommRing K] [CommRing B]
    [Algebra R A] [Algebra R K] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (g : A) [IsLocalization.Away g B] (fs : List A)
    (h : RingTheory.Sequence.IsWeaklyRegular (K ⊗[R] A)
      (fs.map (TensorProduct.includeRight (R := R) (A := K)).toRingHom)) :
    RingTheory.Sequence.IsWeaklyRegular (K ⊗[R] B)
      ((fs.map (algebraMap A B)).map
        (TensorProduct.includeRight (R := R) (A := K)).toRingHom) := by
  let F := K ⊗[R] A
  let z : F := TensorProduct.includeRight g
  let e := IsLocalization.Away.tensorProductEquivTMulRight R K g B
  let L := Localization.Away z
  let : AddCommGroup L := (inferInstance : CommRing L).toAddCommGroup
  have hw := h.of_isLocalization L (Submonoid.powers z)
  have hw' := weak_map_equiv e.symm.toRingEquiv _ hw
  have he (a : A) : e.symm (algebraMap F L (TensorProduct.includeRight a)) =
      TensorProduct.includeRight (algebraMap A B a) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := R) (S := K) A g B 1 a).symm
  have he' (a : A) : e.symm.toRingEquiv
      (algebraMap F L ((TensorProduct.includeRight (R := R) (A := K)).toRingHom a)) =
      (TensorProduct.includeRight (R := R) (A := K)).toRingHom (algebraMap A B a) := he a
  with_reducible_and_instances
    simpa only [List.map_map, Function.comp_def, he'] using hw'

set_option backward.isDefEq.respectTransparency false in
private lemma exists_weak_of_global_fiber
    (n : ℕ) (R A K : Type u) [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] [Module.Flat R A] [FinitePresentation R A]
    (Q : Ideal A) [Q.IsPrime]
    (hK : RingHom.ker (algebraMap R K) = Q.comap (algebraMap R A))
    (fs : List A) (hlen : fs.length = n) (hmem : ∀ f ∈ fs, f ∈ Q)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (K ⊗[R] A)
      (fs.map (TensorProduct.includeRight (R := R) (A := K)).toRingHom)) :
    ∃ g ∉ Q, ∀ (D : Type u) [CommRing D] [Algebra A D] [IsLocalization.Away g D],
      RingTheory.Sequence.IsWeaklyRegular D (fs.map (algebraMap A D)) := by
  induction n generalizing A with
  | zero =>
    have : fs = [] := List.eq_nil_of_length_eq_zero hlen
    subst fs
    exact ⟨1, Ideal.IsPrime.one_notMem inferInstance, fun D _ _ _ ↦ by simp⟩
  | succ n ih =>
    obtain ⟨f, fs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    have hf := ((weak_cons_quotient_iff ((TensorProduct.includeRight (R := R) (A := K) f))
      (fs.map (TensorProduct.includeRight (R := R) (A := K)).toRingHom)).mp hreg).1
    have hfib : ∀ x : A ⊗[R] K, f • x = 0 → (1 : A) • x = 0 := by
      intro x hx
      rw [one_smul]
      let e := TensorProduct.comm R A K
      apply e.injective
      apply hf.right_eq_zero_of_smul
      change (TensorProduct.includeRight (R := R) (A := K) f) * e x = 0
      have he : e (f • x) = (TensorProduct.includeRight (R := R) (A := K) f) * e x := by
        rw [TensorProduct.smul_eq_tmul_one_mul, map_mul]
        rfl
      rw [← he, hx, map_zero]
    obtain ⟨g, hg, hkill⟩ := exists_notMem_forall_mul_mem_map Q f 1
      (Ideal.IsPrime.one_notMem inferInstance) hK hfib
    let B := Localization.Away g
    let : AddCommGroup B := (inferInstance : CommRing B).toAddCommGroup
    have : FinitePresentation A B := IsLocalization.Away.finitePresentation g
    have : FinitePresentation R B := .trans R A B
    let J : Ideal B := Ideal.span {algebraMap A B f}
    let C := B ⧸ J
    have hflat : Module.Flat R C := by
      rw [← RingHom.flat_algebraMap_iff]
      exact (isRegularPrincipal_and_flat_of_forall_mul_mem_map f g hkill B C
        (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (by
          rw [Ideal.mk_ker, Ideal.map_span, Set.image_singleton])).2
    have : FinitePresentation B C := FinitePresentation.quotient (Submodule.fg_span_singleton _)
    have : FinitePresentation R C := .trans R B C
    have hdis : Disjoint (Submonoid.powers g : Set A) Q := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨n, rfl⟩ h
      exact hg (Ideal.IsPrime.mem_of_pow_mem inferInstance n h)
    let QB : Ideal B := Q.map (algebraMap A B)
    have : QB.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers g) B Q inferInstance hdis
    have hQB : QB.comap (algebraMap A B) = Q :=
      IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) B
        inferInstance hdis
    have hJQ : J ≤ QB := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ (hmem f List.mem_cons_self)
    let QC : Ideal C := QB.map (Ideal.Quotient.mk J)
    have : QC.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by simpa using hJQ)
    have hQC : QC.comap (Ideal.Quotient.mk J) = QB := Ideal.comap_map_mk hJQ
    have hKC : RingHom.ker (algebraMap R K) = QC.comap (algebraMap R C) := by
      rw [IsScalarTower.algebraMap_eq R B C, ← Ideal.comap_comap]
      change _ = (QC.comap (Ideal.Quotient.mk J)).comap (algebraMap R B)
      rw [hQC, IsScalarTower.algebraMap_eq R A B, ← Ideal.comap_comap, hQB]
      exact hK
    have hBreg := weak_fiber_localization R A K B g (f :: fs) hreg
    have hCreg := weak_fiber_quotient R B K (algebraMap A B f)
      (fs.map (algebraMap A B)) hBreg
    have hCmem : ∀ x ∈ fs.map (algebraMap A C), x ∈ QC := by
      intro x hx
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hx
      rw [← he, IsScalarTower.algebraMap_apply A B C]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _
        (hmem y (List.mem_cons_of_mem f hy)))
    obtain ⟨v, hv, hvreg⟩ := ih C QC hKC (fs.map (algebraMap A C))
      (by simpa using hlen) hCmem (by
        have he (a : A) : Ideal.Quotient.mk J (algebraMap A B a) =
            algebraMap A C a := (IsScalarTower.algebraMap_apply A B C a).symm
        change RingTheory.Sequence.IsWeaklyRegular (K ⊗[R] C)
          ((fs.map (algebraMap A B)).map (Ideal.Quotient.mk J) |>.map
            (TensorProduct.includeRight (R := R) (A := K)).toRingHom) at hCreg
        convert hCreg using 1
        rw [List.map_map, List.map_map, List.map_map]
        congr 1)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hb : b ∉ QB := fun h ↦ hv (Ideal.mem_map_of_mem _ h)
    let E := Localization.Away b
    let : AddCommGroup E := (inferInstance : CommRing E).toAddCommGroup
    let a := (IsLocalization.Away.sec g b).1
    have ha : Associated (algebraMap A B a) b := IsLocalization.Away.associated_sec_fst g b
    have haQ : a ∉ Q := by
      intro h
      apply hb
      exact (Ideal.mem_iff_of_associated ha).mp (Ideal.mem_map_of_mem _ h)
    have : IsLocalization.Away (g * a) E := IsLocalization.Away.mul_of_associated g a b ha
    let JE : Ideal E := J.map (algebraMap B E)
    have : IsLocalization.Away (Ideal.Quotient.mk J b) (E ⧸ JE) := by
      change IsLocalization.Away (algebraMap B C b) (E ⧸ JE)
      rw [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
      infer_instance
    let : Algebra C (E ⧸ JE) := Ideal.Quotient.algebraQuotientOfLEComap
      (R := B) (A := E) (p := J) (P := JE)
      (fun x hx ↦ Ideal.mem_map_of_mem (algebraMap B E) hx)
    have : IsScalarTower B C (E ⧸ JE) := .of_algebraMap_eq fun _ ↦ rfl
    have ht := hvreg (E ⧸ JE)
    have hhead : IsSMulRegular E (algebraMap A E f) := by
      have hB : IsSMulRegular B (algebraMap A B f) := by
        apply IsSMulRegular.of_right_eq_zero_of_smul
        intro x hx
        exact (mem_nonZeroDivisors_iff.mp
          (algebraMap_mem_nonZeroDivisors_of_forall hkill B)).1 x hx
      have hh := hB.of_flat_of_isBaseChange (IsBaseChange.linearMap B E)
      simpa only [← IsScalarTower.algebraMap_apply A B E] using hh
    have hJE : JE = Ideal.span {algebraMap A E f} := by
      change (Ideal.span {algebraMap A B f}).map (algebraMap B E) = _
      rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply A B E]
    have htail : RingTheory.Sequence.IsWeaklyRegular (E ⧸ Ideal.span {algebraMap A E f})
        ((fs.map (algebraMap A E)).map
          (Ideal.Quotient.mk (Ideal.span {algebraMap A E f}))) := by
      rw [← hJE]
      convert ht using 1
      · with_reducible_and_instances rfl
      · rw [List.map_map, List.map_map]
        congr 1
    have hE : RingTheory.Sequence.IsWeaklyRegular E
        ((f :: fs).map (algebraMap A E)) :=
      (weak_cons_quotient_iff _ _).mpr ⟨hhead, htail⟩
    refine ⟨g * a, Q.primeCompl.mul_mem hg haQ, fun D _ _ _ ↦ ?_⟩
    let e := IsLocalization.algEquiv (Submonoid.powers (g * a)) E D
    have hh := weak_map_equiv e.toRingEquiv _ hE
    have he (x : A) : e.toRingEquiv (algebraMap A E x) = algebraMap A D x := e.commutes x
    simpa only [List.map_map, Function.comp_def, he] using hh

set_option backward.isDefEq.respectTransparency false in
/-- A specified sequence regular in a fibre local ring is regular on a principal
neighbourhood in a flat finitely presented algebra.

Source: Stacks Project, Divisors, Tag 063W, proof of assertion (1), successive
applications of Tag 062Y(3).
(blueprint: lem-pur-fiber-regular-sequence-neighbourhood).

Proof: The fibre algebra is Noetherian. Spread the given regular sequence from
its prime localization to a principal fibre neighbourhood, using Tag 061L.
Clear the base denominators of its shrinking element and invert its numerator
in A. This retains Q. Induct on the length of the specified list, retaining
that every preceding quotient is flat and finitely presented over R. Its fibre
is the quotient of the original fibre by the same preceding equations. The
next equation is a nonzerodivisor there, so the algebraic fibre-Cartier criterion
062Y gives a neighbourhood on which it is a nonzerodivisor and its quotient
is R-flat. Lift each new shrinking element from the prefix quotient and clear
its localization denominator, replacing the ambient shrinking element by the
product. Exactness of localization preserves all earlier injections and
flatness; finite presentation persists under principal localization and finite
quotients. The fibre regularity makes all equations lie in Q, which survives
every shrinking. Thus the final quotient is nonzero. Together with the
successive injections this proves regularity of the specified list. -/
theorem exists_isRegular_of_fiber_local
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [FinitePresentation R A]
    (p : PrimeSpectrum R) (Q : PrimeSpectrum A)
    (P : PrimeSpectrum (p.asIdeal.Fiber A))
    (hP : P.comap TensorProduct.includeRight.toRingHom = Q) (fs : List A)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime P.asIdeal)
      (fs.map fun a ↦ algebraMap (p.asIdeal.Fiber A) (Localization.AtPrime P.asIdeal)
        (TensorProduct.includeRight a))) :
    ∃ g : A, g ∉ Q.asIdeal ∧ RingTheory.Sequence.IsRegular (Localization.Away g)
      (fs.map (algebraMap A (Localization.Away g))) := by
  classical
  let F := p.asIdeal.Fiber A
  have : IsNoetherianRing F := FiniteType.isNoetherianRing p.asIdeal.ResidueField F
  let xs := fs.map (TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField)).toRingHom
  have hreg' : RingTheory.Sequence.IsRegular (Localization.AtPrime P.asIdeal)
      (List.ofFn fun i : Fin xs.length ↦ algebraMap F (Localization.AtPrime P.asIdeal)
        xs[(i : ℕ)]) := by
    rw [List.ofFn_getElem_eq_map xs (algebraMap F (Localization.AtPrime P.asIdeal))]
    change RingTheory.Sequence.IsRegular (Localization.AtPrime P.asIdeal)
      ((fs.map (TensorProduct.includeRight (R := R)
        (A := p.asIdeal.ResidueField)).toRingHom).map
          (algebraMap F (Localization.AtPrime P.asIdeal)))
    rw [List.map_map]
    exact hreg
  obtain ⟨s, hs, hsreg⟩ :=
    RingTheory.exists_isRegular_localizationAway_of_isRegular_localizationAtPrime
      F P.asIdeal xs.length (fun i ↦ xs[(i : ℕ)]) hreg'
  have hsweak : RingTheory.Sequence.IsWeaklyRegular (Localization.Away s)
      (xs.map (algebraMap F (Localization.Away s))) := by
    rw [List.ofFn_getElem_eq_map xs (algebraMap F (Localization.Away s))] at hsreg
    exact hsreg.toIsWeaklyRegular
  have hmem : ∀ f ∈ fs, f ∈ Q.asIdeal := by
    have hproper : (Ideal.ofList xs).map
        (algebraMap F (Localization.AtPrime P.asIdeal)) ≠ ⊤ := by
      rw [Ideal.map_ofList]
      have hh := hreg'.top_ne_smul
      rw [List.ofFn_getElem_eq_map xs (algebraMap F (Localization.AtPrime P.asIdeal))] at hh
      have hp : ⊤ ≠ Ideal.ofList (xs.map (algebraMap F (Localization.AtPrime P.asIdeal))) := by
        simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hh
      exact hp.symm
    have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint P.asIdeal.primeCompl
      (Localization.AtPrime P.asIdeal) (Ideal.ofList xs)).mp hproper
    intro f hf
    rw [← hP]
    by_contra hn
    exact Set.disjoint_left.mp hd hn
      (Ideal.subset_span (List.mem_map.mpr ⟨f, hf, rfl⟩))
  obtain ⟨r, hr, t, hrt⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p.asIdeal s
  have hu : IsUnit (algebraMap R F r) := by
    rw [IsScalarTower.algebraMap_apply R p.asIdeal.ResidueField F]
    exact (isUnit_iff_ne_zero.mpr (fun h ↦ hr
      (Ideal.algebraMap_residueField_eq_zero.mp h))).map (algebraMap p.asIdeal.ResidueField F)
  have hass : Associated (TensorProduct.includeRight t : F) s := by
    have he : algebraMap R F r * s = TensorProduct.includeRight t := by
      change algebraMap R F r * s = (1 ⊗ₜ[R] t : F)
      exact (Algebra.smul_def r s).symm.trans hrt
    rw [← he, mul_comm]
    exact associated_mul_unit_left s _ hu
  have ht : t ∉ Q.asIdeal := by
    rw [← hP]
    intro h
    exact hs ((Ideal.mem_iff_of_associated hass).mp h)
  let B := Localization.Away t
  let : AddCommGroup B := (inferInstance : CommRing B).toAddCommGroup
  have : FinitePresentation A B := IsLocalization.Away.finitePresentation t
  have : FinitePresentation R B := .trans R A B
  have : Module.Flat R B := .trans R A B
  let LF := Localization.Away (1 ⊗ₜ[R] t : F)
  let : AddCommGroup LF := (inferInstance : CommRing LF).toAddCommGroup
  have hass' : Associated (1 ⊗ₜ[R] t : F) s := by
    change Associated (TensorProduct.includeRight t : F) s
    exact hass
  have : IsLocalization.Away s LF := IsLocalization.Away.of_associated hass'
  let el := IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) LF
  have hLF := weak_map_equiv el.toRingEquiv _ hsweak
  have hLF' : RingTheory.Sequence.IsWeaklyRegular LF
      (xs.map (algebraMap F LF)) := by
    have he (x : F) : el.toRingEquiv (algebraMap F (Localization.Away s) x) =
        algebraMap F LF x := el.commutes x
    simpa only [List.map_map, Function.comp_def, he] using hLF
  let e := IsLocalization.Away.tensorProductEquivTMulRight R p.asIdeal.ResidueField t B
  have hB := weak_map_equiv e.symm.toRingEquiv _ hLF'
  have he (a : A) : e.symm.toRingEquiv
      (algebraMap F LF ((TensorProduct.includeRight (R := R)
        (A := p.asIdeal.ResidueField)).toRingHom a)) =
      (TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField)).toRingHom
        (algebraMap A B a) := by
    change e.symm (algebraMap F LF (1 ⊗ₜ[R] a)) = 1 ⊗ₜ[R] (algebraMap A B a)
    apply e.injective
    rw [e.apply_symm_apply]
    exact (IsLocalization.Away.tensorProductEquivTMulRight_tmul
      (R := R) (S := p.asIdeal.ResidueField) A t B 1 a).symm
  have hB' : RingTheory.Sequence.IsWeaklyRegular (p.asIdeal.ResidueField ⊗[R] B)
      ((fs.map (algebraMap A B)).map
        (TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField)).toRingHom) := by
    simpa only [xs, List.map_map, Function.comp_def, he] using hB
  have hd : Disjoint (Submonoid.powers t : Set A) Q.asIdeal := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨n, rfl⟩ h
    exact ht (Ideal.IsPrime.mem_of_pow_mem Q.isPrime n h)
  let QB : Ideal B := Q.asIdeal.map (algebraMap A B)
  have : QB.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers t) B Q.asIdeal Q.isPrime hd
  have hQB : QB.comap (algebraMap A B) = Q.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers t) B Q.isPrime hd
  have hpQ : RingHom.ker (algebraMap R p.asIdeal.ResidueField) =
      Q.asIdeal.comap (algebraMap R A) := by
    rw [Ideal.ker_algebraMap_residueField]
    have h := congrArg PrimeSpectrum.asIdeal hP
    rw [← h]
    change p.asIdeal = (P.asIdeal.comap TensorProduct.includeRight.toRingHom).comap _
    rw [Ideal.comap_comap]
    have hc : TensorProduct.includeRight.toRingHom.comp (algebraMap R A) =
        algebraMap R F := by
      ext x
      exact (TensorProduct.algebraMap_apply' x).symm
    rw [hc]
    exact Ideal.over_def P.asIdeal p.asIdeal
  obtain ⟨v, hv, hvreg⟩ := exists_weak_of_global_fiber fs.length R B
    p.asIdeal.ResidueField QB (by
      rw [IsScalarTower.algebraMap_eq R A B, ← Ideal.comap_comap, hQB]
      exact hpQ) (fs.map (algebraMap A B)) (List.length_map ..)
    (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact Ideal.mem_map_of_mem _ (hmem a ha)) hB'
  let a := (IsLocalization.Away.sec t v).1
  have ha : Associated (algebraMap A B a) v := IsLocalization.Away.associated_sec_fst t v
  have haQ : a ∉ Q.asIdeal := by
    intro h
    exact hv ((Ideal.mem_iff_of_associated ha).mp (Ideal.mem_map_of_mem _ h))
  let D := Localization.Away v
  let : AddCommGroup D := (inferInstance : CommRing D).toAddCommGroup
  have : IsLocalization.Away (t * a) D := IsLocalization.Away.mul_of_associated t a v ha
  have hw : RingTheory.Sequence.IsWeaklyRegular D (fs.map (algebraMap A D)) := by
    have hh := hvreg D
    simpa only [List.map_map, Function.comp_def, ← IsScalarTower.algebraMap_apply A B D]
      using hh
  have hproper : (Ideal.ofList fs).map (algebraMap A D) ≠ ⊤ := by
    apply (IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers (t * a))
      D (Ideal.ofList fs)).mpr
    apply Set.disjoint_left.mpr
    rintro _ ⟨n, rfl⟩ h
    exact (Q.asIdeal.primeCompl.mul_mem ht haQ)
      (Ideal.IsPrime.mem_of_pow_mem Q.isPrime n ((Ideal.span_le.mpr hmem) h))
  have hD : RingTheory.Sequence.IsRegular D (fs.map (algebraMap A D)) := by
    refine ⟨hw, ?_⟩
    simpa only [← Ideal.map_ofList, Ideal.smul_eq_mul, Ideal.mul_top] using hproper.symm
  refine ⟨t * a, Q.asIdeal.primeCompl.mul_mem ht haQ, ?_⟩
  let eD := IsLocalization.algEquiv (Submonoid.powers (t * a)) D
    (Localization.Away (t * a))
  have hh : RingTheory.Sequence.IsRegular (Localization.Away (t * a))
      ((fs.map (algebraMap A D)).map eD.toRingHom) :=
    (eD.toRingEquiv.toAddEquiv.isRegular_congr
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
        (fun x _ y ↦ eD.map_mul x y)))).mp hD
  have heD (x : A) : eD.toRingHom (algebraMap A D x) =
      algebraMap A (Localization.Away (t * a)) x := eD.commutes x
  simpa only [List.map_map, Function.comp_def, heD] using hh

end Algebra
