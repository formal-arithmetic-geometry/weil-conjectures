/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.ProEtale.WeakDimension
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteOverNagata
import WeilConjectures.Mathlib.RingTheory.Etale.Weakly
import WeilConjectures.RingTheory.NagataLocalization
import Sheaf.RingTheory.PolynomialNagata
import Sheaf.RingTheory.NagataOfWeaklyEtale
import Sheaf.RingTheory.WeaklyEtaleLocalComponentDimension

/-!
# Local Nagata properties and universal catenarity under weakly etale maps

Source: Silvio Greco, Two theorems on excellent rings, Nagoya Mathematical Journal 60
(1976), Theorem 5.3(iii), pp. 146–147, with Remark 5.2 and the Foreword on p. 139
(blueprint: lem-exc-weakly-etale-locally-nagata-catenary).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

private theorem weaklyEtale_localization_base
    {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    (M : Submonoid A) [Algebra A A'] [IsLocalization M A']
    [Algebra A B] [Algebra A' B] [IsScalarTower A A' B]
    [Algebra.WeaklyEtale A B] : Algebra.WeaklyEtale A' B where
  flat := (Module.flat_iff_of_isLocalization (S := A') (p := M) (M := B)).mpr inferInstance
  flat_lmul' := by
    have : TensorProduct.CompatibleSMul A A' B B :=
      IsLocalization.tensorProduct_compatibleSMul M A' B B
    let e : TensorProduct A' B B ≃ₐ[A'] TensorProduct A B B :=
      Algebra.TensorProduct.equivOfCompatibleSMul A A' A' B B
    have key : (Algebra.TensorProduct.lmul' A' (S := B)).toRingHom =
        (Algebra.TensorProduct.lmul' A (S := B)).toRingHom.comp e.toRingHom := by
      ext <;> rfl
    change (Algebra.TensorProduct.lmul' A' (S := B)).toRingHom.Flat
    rw [key]
    exact RingHom.Flat.comp (.of_bijective e.bijective) (Algebra.WeaklyEtale.flat_lmul' A B)

private theorem locallyNagata
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (hf : f.WeaklyEtale)
    (hA : ∀ (p : Ideal A) [p.IsPrime], IsNagataRing (Localization.AtPrime p)) :
    ∀ (q : Ideal B) [q.IsPrime], IsNagataRing (Localization.AtPrime q) := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.WeaklyEtale A B := hf
  intro q hq
  let p := q.comap f
  have : p.IsPrime := hq.comap f
  let g := Localization.localRingHom p q f rfl
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := g.toAlgebra
  have : IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_algebraMap_eq fun a ↦ by
      change algebraMap A (Localization.AtPrime q) a = g (algebraMap A _ a)
      rw [Localization.localRingHom_to_map]
      rfl
  have : Algebra.WeaklyEtale B (Localization.AtPrime q) :=
    .of_isLocalization B q.primeCompl _
  have : Algebra.WeaklyEtale A (Localization.AtPrime q) := .trans A B _
  have : Algebra.WeaklyEtale (Localization.AtPrime p) (Localization.AtPrime q) :=
    weaklyEtale_localization_base p.primeCompl
  exact isNagataRing_of_weaklyEtale g inferInstance (hA p)

private theorem catenary_of_contraction
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hR : IsCatenaryRing R)
    (hstrict : ∀ (P Q : Ideal S), P.IsPrime → Q.IsPrime → P < Q →
      P.comap f < Q.comap f)
    (hsat : ∀ (P Q : Ideal S), P.IsPrime → Q.IsPrime → P < Q →
      (¬ ∃ T : Ideal S, T.IsPrime ∧ P < T ∧ T < Q) →
      ¬ ∃ T : Ideal R, T.IsPrime ∧ P.comap f < T ∧ T < Q.comap f) :
    IsCatenaryRing S := by
  have chain : ∀ (P Q : Ideal S) (n : ℕ) (c : Fin (n + 1) → Ideal S),
      IsPrimeChain S P Q n c →
      IsPrimeChain R (P.comap f) (Q.comap f) n (fun i ↦ (c i).comap f) := by
    intro P Q n c hc
    refine ⟨fun i ↦ (hc.1 i).comap f, congrArg (Ideal.comap f) hc.2.1,
      congrArg (Ideal.comap f) hc.2.2.1, ?_⟩
    intro i
    exact hstrict _ _ (hc.1 _) (hc.1 _) (hc.2.2.2 i)
  have saturated : ∀ (P Q : Ideal S) (n : ℕ) (c : Fin (n + 1) → Ideal S),
      IsSaturatedPrimeChain S P Q n c →
      IsSaturatedPrimeChain R (P.comap f) (Q.comap f) n (fun i ↦ (c i).comap f) := by
    intro P Q n c hc
    exact ⟨chain P Q n c hc.1,
      fun i ↦ hsat _ _ (hc.1.1 _) (hc.1.1 _) (hc.1.2.2.2 i) (hc.2 i)⟩
  intro P Q hP hQ hPQ
  have : (P.comap f).IsPrime := hP.comap f
  have : (Q.comap f).IsPrime := hQ.comap f
  obtain ⟨⟨N, hN⟩, heq⟩ := hR (P.comap f) (Q.comap f) (Ideal.comap_mono hPQ)
  refine ⟨⟨N, fun n c hc ↦ hN n _ (chain P Q n c hc)⟩, ?_⟩
  intro n m c d hc hd
  exact heq n m _ _ (saturated P Q n c hc) (saturated P Q m d hd)

private theorem catenary_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hR : IsCatenaryRing R) : IsCatenaryRing S := by
  apply catenary_of_contraction f hR
  · intro P Q _ _ hPQ
    exact (Ideal.orderEmbeddingOfSurjective f hf).strictMono hPQ
  · intro P Q _ _ _ hPQ
    rintro ⟨T, hT, hPT, hTQ⟩
    have : T.IsPrime := hT
    have hker : RingHom.ker f ≤ T :=
      (Ideal.comap_mono (show (⊥ : Ideal S) ≤ P from bot_le)).trans hPT.le
    have hmap : (T.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
    have hcomap : (T.map f).comap f = T := by
      rw [Ideal.comap_map_of_surjective f hf]
      exact sup_eq_left.mpr hker
    apply hPQ
    refine ⟨T.map f, hmap, ?_, ?_⟩
    · apply (Ideal.orderEmbeddingOfSurjective f hf).lt_iff_lt.mp
      simpa only [Ideal.orderEmbeddingOfSurjective_apply, hcomap] using hPT
    · apply (Ideal.orderEmbeddingOfSurjective f hf).lt_iff_lt.mp
      simpa only [Ideal.orderEmbeddingOfSurjective_apply, hcomap] using hTQ

private theorem catenary_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hR : IsCatenaryRing R) :
    IsCatenaryRing S := by
  let e := IsLocalization.orderIsoOfPrime M S
  apply catenary_of_contraction (algebraMap R S) hR
  · intro P Q hP hQ hPQ
    exact e.strictMono (show (⟨P, hP⟩ : {p : Ideal S // p.IsPrime}) < ⟨Q, hQ⟩ from hPQ)
  · intro P Q hP hQ _ hPQ
    rintro ⟨T, hT, hPT, hTQ⟩
    have hdQ := ((IsLocalization.isPrime_iff_isPrime_disjoint M S Q).mp hQ).2
    have hdT : Disjoint (M : Set R) (T : Set R) := hdQ.mono_right hTQ.le
    let t : {p : Ideal R // p.IsPrime ∧ Disjoint (M : Set R) (p : Set R)} :=
      ⟨T, hT, hdT⟩
    apply hPQ
    refine ⟨(e.symm t).1, (e.symm t).2, ?_, ?_⟩
    · change (⟨P, hP⟩ : {p : Ideal S // p.IsPrime}) < e.symm t
      apply e.lt_iff_lt.mp
      change (e ⟨P, hP⟩).1 < (e (e.symm t)).1
      rw [e.apply_symm_apply]
      exact hPT
    · change e.symm t < (⟨Q, hQ⟩ : {p : Ideal S // p.IsPrime})
      apply e.lt_iff_lt.mp
      change (e (e.symm t)).1 < (e ⟨Q, hQ⟩).1
      rw [e.apply_symm_apply]
      exact hTQ

private theorem catenary_finiteType
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (hR : IsUniversallyCatenary R) : IsCatenaryRing S := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  have : Small.{u} S := small_of_surjective hf
  let e := Shrink.algEquiv R S
  have : Algebra.FiniteType R (Shrink.{u} S) :=
    Algebra.FiniteType.of_surjective e.symm.toAlgHom e.symm.surjective
  exact catenary_of_surjective e.toRingHom e.surjective (hR.2 (Shrink.{u} S))

private theorem catenary_essFiniteType
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (hR : IsUniversallyCatenary R) : IsCatenaryRing S := by
  let T := Algebra.EssFiniteType.subalgebra R S
  let M := Algebra.EssFiniteType.submonoid R S
  exact catenary_localization M (catenary_finiteType hR)

private theorem universallyCatenary_essFiniteType
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [IsNoetherianRing S]
    (hR : IsUniversallyCatenary R) : IsUniversallyCatenary S := by
  refine ⟨inferInstance, ?_⟩
  intro T _ _ _
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.EssFiniteType R T := Algebra.EssFiniteType.comp R S T
  exact catenary_essFiniteType hR

private theorem nagata_surjective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hR : IsNagataRing R) : IsNagataRing S := by
  let : Algebra R S := f.toAlgebra
  have : Module.Finite R S := RingHom.Finite.of_surjective f hf
  exact (finite_over_nagata_is_nagata R S hR).1

private theorem nagata_mvPolynomial
    {R : Type*} [CommRing R] (hR : IsNagataRing R) (n : ℕ) :
    IsNagataRing (MvPolynomial (Fin n) R) := by
  induction n with
  | zero =>
      exact nagata_surjective (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm.toRingHom
        (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm.surjective hR
  | succ n ih =>
      exact nagata_surjective (MvPolynomial.finSuccEquiv R n).symm.toRingHom
        (MvPolynomial.finSuccEquiv R n).symm.surjective (isNagataRing_polynomial _ ih)

private theorem nagata_finiteType
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (hR : IsNagataRing R) : IsNagataRing S := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  exact nagata_surjective f.toRingHom hf (nagata_mvPolynomial hR n)

private theorem nagata_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hR : IsNagataRing R) :
    IsNagataRing S := by
  let e := IsLocalization.algEquiv M (Localization M) S
  exact nagata_surjective e.toRingHom e.surjective
    (isNagataRing_localization R M hR).1

private theorem nagata_essFiniteType
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (hR : IsNagataRing R) : IsNagataRing S := by
  let T := Algebra.EssFiniteType.subalgebra R S
  let M := Algebra.EssFiniteType.submonoid R S
  exact nagata_localization M (nagata_finiteType hR)

private theorem locallyNagata_finiteType
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime], IsNagataRing (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime], IsNagataRing (Localization.AtPrime q) := by
  intro q hq
  let p := q.under R
  have : p.IsPrime := inferInstance
  have : q.LiesOver p := ⟨rfl⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType S (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_isLocalization _ q.primeCompl
  have : Algebra.EssFiniteType R (Localization.AtPrime q) :=
    Algebra.EssFiniteType.comp R S _
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R (Localization.AtPrime p) (Localization.AtPrime q)
  exact nagata_essFiniteType (hR p)

private theorem weaklyEtale_equiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra.WeaklyEtale R S] (e : S ≃ₐ[R] T) :
    Algebra.WeaklyEtale R T := by
  let : Algebra S T := e.toRingHom.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq fun r ↦ e.commutes r |>.symm
  have : Algebra.Etale S T := (RingHom.Etale.of_bijective e.bijective).toAlgebra
  exact .trans R S T

private theorem contraction_strict
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.WeaklyEtale R S] (P Q : Ideal S) [P.IsPrime] [Q.IsPrime] (hPQ : P < Q) :
    P.under R < Q.under R := by
  refine lt_of_le_of_ne (Ideal.comap_mono hPQ.le) ?_
  intro heq
  let p := P.under R
  have : p.IsPrime := inferInstance
  let e := PrimeSpectrum.preimageOrderIsoFiber R S (⟨p, inferInstance⟩ : PrimeSpectrum R)
  let a : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {⟨p, inferInstance⟩} :=
    ⟨⟨P, inferInstance⟩, rfl⟩
  let b : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {⟨p, inferInstance⟩} :=
    ⟨⟨Q, inferInstance⟩, PrimeSpectrum.ext heq.symm⟩
  have : Ring.AbsolutelyFlat (p.Fiber S) :=
    .of_flat_lmul' p.ResidueField (p.Fiber S)
      (Algebra.WeaklyEtale.flat_lmul' p.ResidueField (p.Fiber S))
  have ht : Ring.AbsolutelyFlat (p.Fiber S) ↔
      IsReduced (p.Fiber S) ∧ Ring.KrullDimLE 0 (p.Fiber S) :=
    (Ring.AbsolutelyFlat.tfae (p.Fiber S)).out 0 2
  have : Ring.KrullDimLE 0 (p.Fiber S) := (ht.mp inferInstance).2
  have hab : e a < e b := e.strictMono hPQ
  exact hab.ne (PrimeSpectrum.ext
    ((e a).isPrime.isMaximal'.eq_of_le (e b).isPrime.ne_top hab.le))

private theorem quotient_dimensionLEOne
    {R : Type*} [CommRing R] [IsLocalRing R] (p : Ideal R) [p.IsPrime]
    (hp : ¬ ∃ t : Ideal R, t.IsPrime ∧ p < t ∧ t < IsLocalRing.maximalIdeal R) :
    Ring.KrullDimLE 1 (R ⧸ p) := by
  let f := Ideal.Quotient.mk p
  let e := Ideal.orderEmbeddingOfSurjective f Ideal.Quotient.mk_surjective
  have : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
  have : IsLocalHom f := IsLocalHom.of_surjective f Ideal.Quotient.mk_surjective
  apply Ring.KrullDimLE.mk₁'
  intro I hI hprime
  have hi : (I.comap f).IsPrime := hprime.comap f
  have hbot : (⊥ : Ideal (R ⧸ p)).comap f = p := Ideal.mk_ker
  have hlt : p < I.comap f := by
    have he := e.strictMono (bot_lt_iff_ne_bot.mpr hI)
    change (⊥ : Ideal (R ⧸ p)).comap f < I.comap f at he
    simpa only [hbot] using he
  have heq : I.comap f = IsLocalRing.maximalIdeal R := by
    apply eq_of_le_of_not_lt (IsLocalRing.le_maximalIdeal hi.ne_top)
    intro h
    exact hp ⟨I.comap f, hi, hlt, h⟩
  have heq' : I = IsLocalRing.maximalIdeal (R ⧸ p) := by
    apply e.injective
    change I.comap f = (IsLocalRing.maximalIdeal (R ⧸ p)).comap f
    rw [IsLocalRing.maximalIdeal_comap, heq]
  rw [heq']
  infer_instance

private theorem localized_prime
    {R : Type*} [CommRing R] (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    (p.map (algebraMap R (Localization.AtPrime q))).IsPrime ∧
      (p.map (algebraMap R (Localization.AtPrime q))).under R = p := by
  have hd : Disjoint (q.primeCompl : Set R) (p : Set R) :=
    Set.disjoint_left.mpr fun _ hs ht ↦ hs (hpq ht)
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p inferInstance hd,
    IsLocalization.under_map_of_isPrime_disjoint q.primeCompl _ inferInstance hd⟩

private theorem localized_adjacent
    {R : Type*} [CommRing R] (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p < q)
    (hsat : ¬ ∃ t : Ideal R, t.IsPrime ∧ p < t ∧ t < q) :
    ¬ ∃ t : Ideal (Localization.AtPrime q), t.IsPrime ∧
      p.map (algebraMap R (Localization.AtPrime q)) < t ∧
      t < IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  rintro ⟨t, ht, hpt, htq⟩
  let e := IsLocalization.orderEmbedding q.primeCompl (Localization.AtPrime q)
  apply hsat
  refine ⟨t.under R, ht.comap _, ?_, ?_⟩
  · have h := e.strictMono hpt
    change (p.map (algebraMap R (Localization.AtPrime q))).under R < t.under R at h
    rwa [(localized_prime p q hpq.le).2] at h
  · have h := e.strictMono htq
    change t.under R < (IsLocalRing.maximalIdeal (Localization.AtPrime q)).under R at h
    simpa only [Localization.AtPrime.under_maximalIdeal] using h

private theorem weaklyEtale_quotient
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.WeaklyEtale R S] (I : Ideal R) :
    Algebra.WeaklyEtale (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
  exact weaklyEtale_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm

private theorem adjacent_of_quotient_dimensionLEOne
    {R : Type*} [CommRing R] [IsLocalRing R] (p : Ideal R) [p.IsPrime]
    [Ring.KrullDimLE 1 (R ⧸ p)] :
    ¬ ∃ t : Ideal R, t.IsPrime ∧ p < t ∧ t < IsLocalRing.maximalIdeal R := by
  rintro ⟨t, ht, hpt, htm⟩
  have : t.IsPrime := ht
  let f := Ideal.Quotient.mk p
  let K := t.map f
  have : K.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa only [Ideal.mk_ker] using hpt.le)
  have hK : K.comap f = t := Ideal.comap_map_mk hpt.le
  have hne : K ≠ ⊥ := by
    intro h
    have hb : (⊥ : Ideal (R ⧸ p)).comap f = p := Ideal.mk_ker
    exact hpt.ne (hK.symm.trans ((congrArg (Ideal.comap f) h).trans hb)).symm
  have : K.IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot inferInstance hne
  have : t.IsMaximal := hK ▸ Ideal.comap_isMaximal_of_surjective f
    Ideal.Quotient.mk_surjective
  exact htm.ne (Ideal.IsMaximal.eq_of_le inferInstance
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top htm.le)

private theorem contraction_adjacent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.WeaklyEtale R S]
    (hR : IsUniversallyCatenary R)
    (hn : ∀ (p : Ideal R) [p.IsPrime], IsNagataRing (Localization.AtPrime p))
    (P Q : Ideal S) [P.IsPrime] [Q.IsPrime] (hPQ : P < Q)
    (hsat : ¬ ∃ T : Ideal S, T.IsPrime ∧ P < T ∧ T < Q) :
    ¬ ∃ T : Ideal R, T.IsPrime ∧ P.under R < T ∧ T < Q.under R := by
  let p := P.under R
  let q := Q.under R
  have : p.IsPrime := inferInstance
  have : q.IsPrime := inferInstance
  have hpq : p < q := contraction_strict P Q hPQ
  let R' := Localization.AtPrime q
  let S' := Localization.AtPrime Q
  let g := Localization.localRingHom q Q (algebraMap R S) rfl
  let : Algebra R' S' := g.toAlgebra
  have hcomm : g.comp (algebraMap R R') =
      (algebraMap S S').comp (algebraMap R S) := by
    ext x
    rw [RingHom.comp_apply, Localization.localRingHom_to_map]
    rfl
  have : IsScalarTower R R' S' := .of_algebraMap_eq fun x ↦ (congrArg (· x) hcomm).symm
  have : Algebra.WeaklyEtale S S' := .of_isLocalization S Q.primeCompl S'
  have : Algebra.WeaklyEtale R S' := .trans R S S'
  have : Algebra.WeaklyEtale R' S' := weaklyEtale_localization_base q.primeCompl
  let a := p.map (algebraMap R R')
  let c := P.map (algebraMap S S')
  have : a.IsPrime := (localized_prime p q hpq.le).1
  have : c.IsPrime := (localized_prime P Q hPQ.le).1
  have hca : c.comap g = a := by
    apply (IsLocalization.orderEmbedding q.primeCompl R').injective
    change (c.comap g).comap (algebraMap R R') = a.under R
    rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
    change (c.under S).under R = a.under R
    rw [(localized_prime P Q hPQ.le).2, (localized_prime p q hpq.le).2]
  let b := a.map (algebraMap R' S')
  have hbc : b ≤ c := Ideal.map_le_iff_le_comap.mpr hca.ge
  let C := R' ⧸ a
  let D := S' ⧸ b
  have : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top (inferInstance : c.IsPrime)) hbc)
  have : IsLocalRing C := IsLocalRing.of_surjective' (Ideal.Quotient.mk a)
    Ideal.Quotient.mk_surjective
  have : IsLocalRing D := IsLocalRing.of_surjective' (Ideal.Quotient.mk b)
    Ideal.Quotient.mk_surjective
  have : Algebra.WeaklyEtale C D := weaklyEtale_quotient a
  let h : C →+* D := algebraMap C D
  have : IsLocalHom (Ideal.Quotient.mk b) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom h := by
    constructor
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (isUnit_of_map_unit g x
      (isUnit_of_map_unit (Ideal.Quotient.mk b) (g x) hx)).map (Ideal.Quotient.mk a)
  let J := c.map (Ideal.Quotient.mk b)
  have : J.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa only [Ideal.mk_ker] using hbc)
  have hJc : J.comap (Ideal.Quotient.mk b) = c := Ideal.comap_map_mk hbc
  have hJh : J.under C = ⊥ := by
    apply (Ideal.orderEmbeddingOfSurjective (Ideal.Quotient.mk a)
      Ideal.Quotient.mk_surjective).injective
    change (J.comap h).comap (Ideal.Quotient.mk a) =
      (⊥ : Ideal C).comap (Ideal.Quotient.mk a)
    have hcom : h.comp (Ideal.Quotient.mk a) = (Ideal.Quotient.mk b).comp g := rfl
    rw [Ideal.comap_comap, hcom, ← Ideal.comap_comap, hJc, hca]
    exact Ideal.mk_ker.symm
  have hJmin : J ∈ minimalPrimes D := by
    rw [minimalPrimes_eq_minimals]
    refine ⟨inferInstance, ?_⟩
    intro K hK hKJ
    have : K.IsPrime := hK
    by_contra hle
    have hc := contraction_strict (R := C) (S := D) K J
      (lt_iff_le_not_ge.mpr ⟨hKJ, hle⟩)
    rw [hJh] at hc
    exact not_lt_bot hc
  have : Module.Finite C (integralClosure C (FractionRing C)) :=
    isN1_of_isN2 C (FractionRing C) ((hn q).2 a)
  have hCcat : IsUniversallyCatenary C := universallyCatenary_essFiniteType
    (universallyCatenary_essFiniteType (S := R') hR)
  have hd := RingHom.WeaklyEtale.ringKrullDim_quotient_minimalPrime_eq
    h (RingHom.weaklyEtale_algebraMap_iff |>.mpr inferInstance) hCcat J hJmin
  have : Ring.KrullDimLE 1 (S' ⧸ c) := quotient_dimensionLEOne c
    (localized_adjacent P Q hPQ hsat)
  have hdim : ringKrullDim C ≤ 1 := by
    rw [← hd, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hbc)]
    exact Ring.krullDimLE_iff.mp inferInstance
  have : Ring.KrullDimLE 1 C := Ring.krullDimLE_iff.mpr hdim
  intro H
  obtain ⟨T, hT, hpT, hTq⟩ := H
  have : T.IsPrime := hT
  let t := T.map (algebraMap R R')
  have : t.IsPrime := (localized_prime T q hTq.le).1
  apply adjacent_of_quotient_dimensionLEOne a
  refine ⟨t, inferInstance, ?_, ?_⟩
  · apply (IsLocalization.orderEmbedding q.primeCompl R').lt_iff_lt.mp
    change a.under R < t.under R
    rw [(localized_prime p q hpq.le).2, (localized_prime T q hTq.le).2]
    exact hpT
  · apply (IsLocalization.orderEmbedding q.primeCompl R').lt_iff_lt.mp
    change t.under R < (IsLocalRing.maximalIdeal R').under R
    rw [(localized_prime T q hTq.le).2, Localization.AtPrime.under_maximalIdeal]
    exact hTq

private theorem catenary_weaklyEtale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.WeaklyEtale R S]
    (hR : IsUniversallyCatenary R)
    (hn : ∀ (p : Ideal R) [p.IsPrime], IsNagataRing (Localization.AtPrime p)) :
    IsCatenaryRing S := by
  apply catenary_of_contraction (algebraMap R S) (hR.2 R)
  · intro P Q hP hQ hPQ
    have : P.IsPrime := hP
    have : Q.IsPrime := hQ
    exact contraction_strict P Q hPQ
  · intro P Q hP hQ hPQ hsat
    have : P.IsPrime := hP
    have : Q.IsPrime := hQ
    exact contraction_adjacent hR hn P Q hPQ hsat

/-- Universal catenarity and the Nagata property of every prime localization ascend
along a weakly etale homomorphism of commutative Noetherian rings.

Source: Greco, Two theorems on excellent rings, Theorem 5.3(iii), pp. 146–147;
Remark 5.2 identifies absolute flatness with weak etaleness for Noetherian rings
(blueprint: lem-exc-weakly-etale-locally-nagata-catenary).

Proof (the nine steps of the recorded DAG proof):
1. For a prime q of B, let p be its contraction to A. Localize the target at q and the base at
   p. Composition with localization preserves weak etaleness. To restrict the base from A to
   A_p, use flatness over a localization and the compatible tensor equivalence B_q tensor_{A_p}
   B_q = B_q tensor_A B_q. This also handles different universes for A and B.

2. Apply Nagata ascent to the resulting weakly etale map A_p to B_q. Both localizations are
   Noetherian, and A_p is Nagata by hypothesis. This proves the local Nagata clause.

3. For each n, form R = A[X_1,...,X_n] and S = B[X_1,...,X_n]. The map R to S is weakly etale by
   polynomial base change. Both rings are Noetherian. Essential finite type permanence makes R
   universally catenary. Nagata permanence under polynomial extension, quotient and localization
   makes R locally Nagata: for a prime r contracting to a, R_r is essentially finite type over
   the Nagata ring A_a.

4. Comparable primes in S with the same contraction correspond, by the fibre prime order
   isomorphism, to comparable primes of the residue-field fibre. Base change makes this fibre
   weakly etale over a field. The proved absolutely-flat API gives Krull dimension at most zero
   for the fibre, so every prime is maximal. The comparable fibre primes coincide. Thus strict
   inclusions of primes contract strictly.

5. Catenarity passes through surjections and localizations by contraction: strict prime chains
   and saturated chains remain strict and saturated, since every intermediate contracted prime
   lifts. Hence both the bound on chain lengths and equality of saturated-chain lengths pass to
   the target. An essentially finite type algebra is a localization of a finite type subalgebra,
   so it is catenary over a universally catenary base. Composing with finite type extensions
   proves universal catenarity for Noetherian essentially finite type algebras. A polynomial
   presentation and Shrink.algEquiv handle the different universes in the finite type
   quantifier.

6. For adjacent primes P < Q of S, let p < q be their contractions. Put Rprime = R_q, Sprime =
   S_Q, a = p Rprime, c = P Sprime, and b = a Sprime. Localization prime correspondence gives c
   contracting to a, so b is contained in c. Set C = Rprime/a and D = Sprime/b. Then C is a
   Noetherian local domain and D a nonzero Noetherian local ring. The induced map C to D is
   local and weakly etale by localization and quotient base change. Step 5 makes C universally
   catenary. The Nagata hypothesis at q makes C Japanese, giving finite normalization in its
   fraction field.

7. Let J be the image of c in D. It is prime and contracts to zero in C. Step 4 excludes a prime
   strictly below J, so J is minimal. Adjacency of P < Q gives Krull dimension at most one for
   Sprime/c. The local component dimension theorem gives dim(D/J) = dim C, and the double-
   quotient equivalence identifies D/J with Sprime/c. Therefore C has dimension at most one. A
   prime strictly between p and q would localize and descend to a nonzero nonmaximal prime of C,
   a contradiction. Contracted adjacent primes are thus adjacent.

8. Contract each finite prime chain of S to R. Step 4 preserves strictness and length; steps 6
   and 7 preserve saturation. Catenarity of R supplies both the bound on lengths and equality of
   lengths of saturated chains, proving catenarity of S. This argument includes zero-length
   chains and empty spectra.

9. Every finite type B-algebra is a quotient of some polynomial ring S as in step 3. Steps 3
   through 8 make S catenary, and the surjective case of step 5 makes its quotient catenary.
   Thus B is universally catenary. Combine this with step 2. -/
theorem isUniversallyCatenary_and_locallyNagata_of_weaklyEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (hf : f.WeaklyEtale)
    (hA : ∀ (p : Ideal A) [p.IsPrime], IsNagataRing (Localization.AtPrime p))
    (hcat : IsUniversallyCatenary A) :
    IsUniversallyCatenary B ∧
      ∀ (q : Ideal B) [q.IsPrime], IsNagataRing (Localization.AtPrime q) := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.WeaklyEtale A B := hf
  refine ⟨⟨inferInstance, ?_⟩, locallyNagata f hf hA⟩
  intro T _ _ _
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType B T)
  let R := MvPolynomial (Fin n) A
  let S := MvPolynomial (Fin n) B
  let : Algebra R S := MvPolynomial.algebraMvPolynomial
  have : Algebra.WeaklyEtale R S :=
    weaklyEtale_equiv (Algebra.IsPushout.equiv A R B S)
  have hR : IsUniversallyCatenary R := universallyCatenary_essFiniteType hcat
  have hn : ∀ (p : Ideal R) [p.IsPrime], IsNagataRing (Localization.AtPrime p) :=
    locallyNagata_finiteType hA
  exact catenary_of_surjective g.toRingHom hg (catenary_weaklyEtale hR hn)

end RingHom
