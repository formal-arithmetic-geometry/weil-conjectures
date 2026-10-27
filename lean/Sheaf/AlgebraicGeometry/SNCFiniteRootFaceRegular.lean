/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.SNCRootLocalPresentation
import Sheaf.RingTheory.TransverseLocalRootFamilyRegular
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal

/-!
# Regularity of coordinate faces of finite SNC root algebras

Source: ILO, Travaux de Gabber, Expose IX, Proposition 2.1 proof, printed p.133;
Stacks Project, Tag 0BIA, `lemma-strict-normal-crossings`.
(blueprint: lem-sfb-snc-finite-root-face-regular).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

private noncomputable abbrev rootIdeal {A : Type u} [CommRing A] {I : Type*}
    (t : I → A) (n : ℕ) : Ideal (MvPolynomial I A) :=
  Ideal.span (Set.range (fun i ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))

private noncomputable abbrev faceIdeal {A : Type u} [CommRing A] {I : Type*}
    (t : I → A) (n : ℕ) (J : Set I) : Ideal (MvPolynomial I A) :=
  rootIdeal t n ⊔ Ideal.span (MvPolynomial.X '' J)

private theorem face_relation {A : Type u} [CommRing A] {I : Type*}
    (t : I → A) (n : ℕ) (J : Set I) (i : I) :
    (Ideal.Quotient.mk (faceIdeal t n J) (MvPolynomial.X i)) ^ n =
      Ideal.Quotient.mk (faceIdeal t n J) (MvPolynomial.C (t i)) := by
  apply sub_eq_zero.mp
  rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_range_self i))

private theorem face_coordinate {A : Type u} [CommRing A] {I : Type*}
    (t : I → A) (n : ℕ) (J : Set I) (i : I) (hi : i ∈ J) :
    Ideal.Quotient.mk (faceIdeal t n J) (MvPolynomial.X i) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, hi, rfl⟩)

private theorem face_parameter {A : Type u} [CommRing A] {I : Type*}
    (t : I → A) (n : ℕ) (hn : 0 < n) (J : Set I) (i : I) (hi : i ∈ J) :
    Ideal.Quotient.mk (faceIdeal t n J) (MvPolynomial.C (t i)) = 0 := by
  rw [← face_relation, face_coordinate t n J i hi, zero_pow (Nat.ne_of_gt hn)]

private theorem transverse_relation {A : Type*} [CommRing A] {I : Type*}
    (t : I → A) (n : ℕ) (J K : Finset I) (i : K) :
    let b := Ideal.Quotient.mk (RingTheory.transverseRootRelationIdeal t n J K)
    b (MvPolynomial.X i) ^ n =
      b (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span (t '' (J : Set I))) (t i))) := by
  dsimp only
  apply sub_eq_zero.mp
  rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_range_self i)

private theorem face_presentation {A : Type u} [CommRing A] {I : Type*} [Fintype I] [DecidableEq I]
    (t : I → A) (n : ℕ) (hn : 0 < n) (J : Finset I) :
    Nonempty ((MvPolynomial I A ⧸ faceIdeal t n (J : Set I)) ≃+*
      RingTheory.transverseRootAlgebra t n J (Finset.univ \ J)) := by
  classical
  let K := Finset.univ \ J
  let U := RingTheory.transverseRootCoefficientRing t J
  let B := RingTheory.transverseRootAlgebra t n J K
  let E := MvPolynomial I A ⧸ faceIdeal t n (J : Set I)
  let q : A →+* U := Ideal.Quotient.mk _
  let b : MvPolynomial K U →+* B := Ideal.Quotient.mk _
  let a : MvPolynomial I A →+* E := Ideal.Quotient.mk _
  let f : MvPolynomial I A →+* B := MvPolynomial.eval₂Hom
    ((b.comp MvPolynomial.C).comp q)
    (fun i ↦ if hi : i ∈ J then 0 else b (MvPolynomial.X ⟨i, by simp [K, hi]⟩))
  have hf : faceIdeal t n (J : Set I) ≤ RingHom.ker f := by
    refine sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨i, rfl⟩
      change f (MvPolynomial.X i ^ n - MvPolynomial.C (t i)) = 0
      by_cases hi : i ∈ J
      · have ht : q (t i) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, hi, rfl⟩)
        simp [f, hi, ht, Nat.ne_of_gt hn]
      · let k : K := ⟨i, by simp [K, hi]⟩
        change f (MvPolynomial.X i ^ n - MvPolynomial.C (t i)) = 0
        rw [map_sub, map_pow]
        have hfx : f (MvPolynomial.X i) = b (MvPolynomial.X k) := by simp [f, hi, k]
        have hfc : f (MvPolynomial.C (t i)) = b (MvPolynomial.C (q (t i))) := by simp [f]
        rw [hfx, hfc]
        exact sub_eq_zero.mpr (transverse_relation t n J K k)
    · rintro _ ⟨i, hi, rfl⟩
      change f (MvPolynomial.X i) = 0
      simp [f, show i ∈ J from hi]
  let F : E →+* B := Ideal.Quotient.lift _ f hf
  let c : U →+* E := Ideal.Quotient.lift _ (a.comp MvPolynomial.C) (by
    change Ideal.span (t '' (J : Set I)) ≤ RingHom.ker (a.comp MvPolynomial.C)
    apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact face_parameter t n hn (J : Set I) i hi)
  let g : MvPolynomial K U →+* E := MvPolynomial.eval₂Hom c (fun i ↦ a (MvPolynomial.X i.val))
  have hg : RingTheory.transverseRootRelationIdeal t n J K ≤ RingHom.ker g := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change g (MvPolynomial.X i ^ n - MvPolynomial.C (q (t i))) = 0
    rw [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
    change (a (MvPolynomial.X i.val)) ^ n - c (q (t i.val)) = 0
    change (a (MvPolynomial.X i.val)) ^ n - a (MvPolynomial.C (t i.val)) = 0
    exact sub_eq_zero.mpr (face_relation t n (J : Set I) i.val)
  let G : B →+* E := Ideal.Quotient.lift _ g hg
  have hGF : G.comp F = RingHom.id E := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro x
      change G (F (a (MvPolynomial.C x))) = a (MvPolynomial.C x)
      change G (f (MvPolynomial.C x)) = a (MvPolynomial.C x)
      rw [show f (MvPolynomial.C x) = b (MvPolynomial.C (q x)) by simp [f]]
      change g (MvPolynomial.C (q x)) = a (MvPolynomial.C x)
      rw [MvPolynomial.eval₂Hom_C]
      rfl
    · intro i
      change G (F (a (MvPolynomial.X i))) = a (MvPolynomial.X i)
      change G (f (MvPolynomial.X i)) = a (MvPolynomial.X i)
      by_cases hi : i ∈ J
      · rw [show f (MvPolynomial.X i) = 0 by simp [f, hi], map_zero]
        exact (face_coordinate t n (J : Set I) i hi).symm
      · rw [show f (MvPolynomial.X i) = b (MvPolynomial.X ⟨i, by simp [K, hi]⟩) by
          simp [f, hi]]
        change g (MvPolynomial.X ⟨i, _⟩) = a (MvPolynomial.X i)
        exact MvPolynomial.eval₂Hom_X' _ _ _
  have hFG : F.comp G = RingHom.id B := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change F (G (b (MvPolynomial.C (q x)))) = b (MvPolynomial.C (q x))
      change F (g (MvPolynomial.C (q x))) = b (MvPolynomial.C (q x))
      rw [MvPolynomial.eval₂Hom_C]
      change f (MvPolynomial.C x) = b (MvPolynomial.C (q x))
      simp [f]
    · intro i
      have hi : i.val ∉ J := (Finset.mem_sdiff.mp i.property).2
      change F (g (MvPolynomial.X i)) = b (MvPolynomial.X i)
      rw [MvPolynomial.eval₂Hom_X']
      change f (MvPolynomial.X i.val) = b (MvPolynomial.X i)
      simp [f, hi]
  exact ⟨RingEquiv.ofRingHom F G hFG hGF⟩

private theorem face_map {A R : Type*} [CommRing A] [CommRing R]
    {I : Type*} (t : I → A) (n : ℕ) (J : Set I) (f : A →+* R) :
    (faceIdeal t n J).map (MvPolynomial.map f) = faceIdeal (fun i ↦ f (t i)) n J := by
  simp only [faceIdeal, rootIdeal, Ideal.map_sup, Ideal.map_span, ← Set.range_comp,
    map_sub, map_pow, MvPolynomial.map_X, MvPolynomial.map_C, Set.image_image,
    Function.comp_def]

private theorem regular_at_of_localization {E : Type*} [CommRing E]
    (q : Ideal E) [q.IsPrime] (M : Submonoid E) (hM : Disjoint (M : Set E) (q : Set E))
    (hreg : IsRegularRing (Localization M)) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let Q := q.map (algebraMap E (Localization M))
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M (Localization M) q
    inferInstance hM
  have hQ : Q.comap (algebraMap E (Localization M)) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M (Localization M) inferInstance hM
  let := hreg
  have : IsRegularLocalRing (Localization.AtPrime Q) := inferInstance
  have : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    simpa only [hQ] using
      (inferInstance : IsLocalization.AtPrime (Localization.AtPrime Q)
        (Q.comap (algebraMap E (Localization M))))
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime Q)
      (Localization.AtPrime q)).toRingEquiv

private theorem localized_face_regular {A : Type*} [CommRing A]
    {I : Type*} [Fintype I] [DecidableEq I] (t : I → A) (n : ℕ) (hn : 0 < n)
    (J : Finset I) (p : Ideal A) [p.IsPrime]
    (hreg : IsRegularRing (RingTheory.transverseRootAlgebra
      (fun i ↦ algebraMap A (Localization.AtPrime p) (t i)) n J (Finset.univ \ J))) :
    IsRegularRing (Localization
      (p.primeCompl.map (algebraMap A (MvPolynomial I A ⧸ faceIdeal t n (J : Set I))))) := by
  let R := Localization.AtPrime p
  let P := MvPolynomial I A
  let P' := MvPolynomial I R
  let E := P ⧸ faceIdeal t n (J : Set I)
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  let D := P' ⧸ (faceIdeal t n (J : Set I)).map (algebraMap P P')
  let M := p.primeCompl.map (MvPolynomial.C : A →+* P)
  have : IsLocalization M P' := MvPolynomial.isLocalization p.primeCompl R
  let N := M.map (algebraMap P E)
  have : IsLocalization N D :=
    IsLocalization.of_surjective M P' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have hmap : (faceIdeal t n (J : Set I)).map (algebraMap P P') =
      faceIdeal (fun i ↦ algebraMap A R (t i)) n (J : Set I) :=
    face_map t n (J : Set I) (algebraMap A R)
  let e : D ≃+* (P' ⧸ faceIdeal (fun i ↦ algebraMap A R (t i)) n (J : Set I)) :=
    Ideal.quotEquivOfEq hmap
  obtain ⟨e'⟩ := face_presentation (fun i ↦ algebraMap A R (t i)) n hn J
  let := hreg
  have : IsRegularRing D := IsRegularRing.of_ringEquiv (e.trans e').symm
  have : IsRegularRing (Localization N) := IsRegularRing.of_ringEquiv
    (IsLocalization.algEquiv N D (Localization N)).toRingEquiv
  have hN : N = p.primeCompl.map (algebraMap A E) := by
    dsimp [N, M]
    ext x
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨MvPolynomial.C a, ⟨a, ha, rfl⟩, rfl⟩
  exact hN ▸ (inferInstance : IsRegularRing (Localization N))

private theorem branch_enumeration
    (A : Type u) [CommRing A] (r : ℕ) (t : Fin r → A)
    (H : (Spec (.of A)).IdealSheafData)
    (hreduced : ∀ i, _root_.IsReduced (A ⧸ Ideal.span ({t i} : Set A)))
    (hdistinct : Function.Injective
      (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A))))) :
    ∃ components : Fin r ≃ {Z : Set (H.support : Set (Spec (.of A))) //
        Z ∈ irreducibleComponents (H.support : Set (Spec (.of A)))},
      ∀ i, (Ideal.span {t i}).IsPrime ∧
        Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t i})))) =
          Subtype.val '' (components i).val := by
  classical
  have hc : ∀ i : Fin r, ∃ Z, Z ∈ irreducibleComponents
      (H.support : Set (Spec (.of A))) ∧
      Subtype.val '' Z = PrimeSpectrum.zeroLocus ({t i} : Set A) := by
    intro i
    have hi := Set.mem_range_self (f := fun i : Fin r ↦
      PrimeSpectrum.zeroLocus ({t i} : Set A)) i
    rw [hbranches] at hi
    exact hi
  choose C hC heq using hc
  have himage : Function.Injective
      (Set.image (Subtype.val : ↥(H.support : Set (Spec (.of A))) → Spec (.of A))) :=
    Set.image_injective.mpr Subtype.val_injective
  let e : Fin r ≃ {Z : Set (H.support : Set (Spec (.of A))) //
      Z ∈ irreducibleComponents (H.support : Set (Spec (.of A)))} :=
    Equiv.ofBijective (fun i ↦ ⟨C i, hC i⟩) ⟨by
      intro i j hij
      apply hdistinct
      change PrimeSpectrum.zeroLocus ({t i} : Set A) =
        PrimeSpectrum.zeroLocus ({t j} : Set A)
      rw [← heq i, ← heq j]
      exact congrArg (fun z ↦ Subtype.val '' z.val) hij, by
      intro Z
      have hz : Subtype.val '' Z.val ∈ Set.range (fun i : Fin r ↦
          PrimeSpectrum.zeroLocus ({t i} : Set A)) := by
        rw [hbranches]
        exact ⟨Z.val, Z.property, rfl⟩
      obtain ⟨i, hi⟩ := hz
      refine ⟨i, Subtype.ext (himage ?_)⟩
      exact (heq i).trans hi⟩
  refine ⟨e, fun i ↦ ⟨?_, ?_⟩⟩
  · have hi : IsIrreducible (PrimeSpectrum.zeroLocus ({t i} : Set A)) := by
      rw [← heq i]
      exact (hC i).1.image _ continuous_subtype_val.continuousOn
    have hrad : (Ideal.span ({t i} : Set A)).IsRadical :=
      (Ideal.isRadical_iff_quotient_reduced _).mpr (hreduced i)
    rw [← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.isIrreducible_zeroLocus_iff,
      hrad.radical] at hi
    exact hi
  · change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {t i}))) = _
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
    exact (heq i).symm

/-- Every coordinate face of a simultaneous root algebra along the distinct reduced
branches of an SNC boundary on a regular affine scheme is a regular Noetherian ring.
The second quotient kills exactly the images of the coordinates indexed by J.
Empty or disconnected intersections, the empty tuple, and the zero ring are allowed.

Source: ILO IX, Proposition 2.1 proof, printed p.133; Stacks Tag 0BIA.
(blueprint: lem-sfb-snc-finite-root-face-regular).

Proof:
1. Setting the coordinates indexed by J to zero identifies the face ring E_J with
   (A/(t_j : j in J))[x_i : i outside J]/(x_i^n-t_i). The mutually inverse maps
   send coefficients and surviving roots to their classes. Since n is positive,
   the killed root relations impose exactly t_j = 0. Local Noetherianity of A's
   spectrum gives Noetherianity of A by `pqf-lem-affine-open-locnoeth`, and finite
   presentation gives Noetherianity of E_J by
   `lem-weil-pbc-finite-type-algebra-noetherian`.
2. For a prime q of E_J contract to p in A, put R = A_p, and let S index the
   equations belonging to p; J is contained in S. For every L contained in S,
   R_L = R/(t_l : l in L) is regular local, of dimension dim(R)-card(L), by the
   SNC intersection criterion, `lem-weil-pbc-affine-open-stalk-localization`, and
   `lem-weil-pbc-localization-at-prime-of-quotient`. Equations outside S are units.
3. For every L contained in S and K disjoint from L, form B_{L,K} by adjoining the
   roots indexed by K over R_L. Induct simultaneously over L on card(K). These
   rings are Noetherian by `lem-weil-pbc-finite-type-algebra-noetherian`.
   Iterating `lem-weil-pbc-monic-quotient-free` gives the free monomial basis with
   all exponents less than n. Reordering the presentations fixes every generator.
   For empty K regularity follows from `lem-weil-pbc-regular-local-localization`.
4. Choose i in nonempty K, put D = B_{L,K minus i}, and B = D[T]/(T^n-t_i), with
   root u. D is regular by induction. If a prime Q contains u, then i belongs
   to S minus L. The dimension equalities for L and L union i imply t_i is
   nonzero in R_L. The regular local ring R_L is a domain by
   `lem-sc-regular-local-domain`, so t_i acts injectively on R_L and hence on
   its free module D, coefficient by coefficient in the monomial basis.
5. Quotienting D by t_i gives B_{L union i,K minus i}; the inverse presentation
   maps fix coefficients and surviving roots, as also follows from the quotient
   compatibility in `lem-weil-pbc-monic-quotient-free`. This is regular by the
   smaller-root induction. Apply `lem-sbc-root-algebra-regular-at-root` using
   Noetherianity, injective multiplication by t_i, and this regular quotient.
   It gives regularity of B_Q at primes containing u.
6. At a prime Q missing u, also t_i is outside Q. F = D[1/t_i] is regular by
   `lem-weil-pbc-localization-of-regular-ring`, and F[T] is regular by
   `lem-trf-polynomial-ring-regular-base`. In F[T]/(T^n-t_i), T has inverse
   T^(n-1)/t_i, and the derivative n*T^(n-1) is a unit. Thus
   `lem-weil-pbc-hypersurface-derivation-regular` makes this ring regular.
   It is B[1/t_i], and its localization at Q is B_Q by inverse fraction maps.
   This proves the simultaneous induction step at every prime.
7. Take L = J and K the complementary indices. The presentation in step 1
   identifies B_{J,K} with the localization of E_J away from p, by inverse maps
   fixing coefficients and roots. Localizing further at q gives (E_J)_q.
   Every prime localization is therefore regular local; E_J is Noetherian by
   step 1, so it is regular in the sense of `def-weil-regular-scheme`.
   For an empty stratum E_J is zero and has no primes. The argument also covers
   disconnected strata, J empty, r = 0, A = 0, and n = 1.
-/
theorem isRegularRing_snc_finiteRoot_face
    (A : Type u) [CommRing A] (hA : IsRegularScheme (Spec (.of A)))
    (r : ℕ) (t : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hreduced : ∀ i : Fin r, _root_.IsReduced (A ⧸ Ideal.span ({t i} : Set A)))
    (hdistinct : Function.Injective
      (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : A)) (J : Set (Fin r)) :
    IsRegularRing ((MvPolynomial (Fin r) A ⧸
      Ideal.span (Set.range (fun i : Fin r ↦
        (MvPolynomial.X i : MvPolynomial (Fin r) A) ^ n - MvPolynomial.C (t i)))) ⧸
      Ideal.map (Ideal.Quotient.mk
        (Ideal.span (Set.range (fun i : Fin r ↦
          (MvPolynomial.X i : MvPolynomial (Fin r) A) ^ n - MvPolynomial.C (t i)))))
        (Ideal.span ((fun j : Fin r ↦ (MvPolynomial.X j : MvPolynomial (Fin r) A)) '' J))) := by
  classical
  obtain ⟨components, hc⟩ := branch_enumeration A r t H hreduced hdistinct hbranches
  obtain ⟨hnoeth, _, hlocal⟩ := snc_root_local_presentation A hA r t H hH
    components hc n hn
  let := hnoeth
  let J' : Finset (Fin r) := J.toFinset
  have hJ' : (J' : Set (Fin r)) = J := Set.coe_toFinset J
  let E := MvPolynomial (Fin r) A ⧸ faceIdeal t n (J' : Set (Fin r))
  have : IsNoetherianRing E := inferInstance
  have hE : IsRegularRing E := by
    apply isRegularRing_iff.mpr
    intro q hq
    let p := q.comap (algebraMap A E)
    have : p.IsPrime := Ideal.comap_isPrime _ q
    let R := Localization.AtPrime p
    let t' : Fin r → R := fun i ↦ algebraMap A R (t i)
    have : IsRegularLocalRing R := by
      let := hA.2
      exact IsRegularLocalRing.of_ringEquiv
        (Spec.stalkIso (.of A) ⟨p, inferInstance⟩).commRingCatIsoToRingEquiv
    have hs : ∀ L : Finset (Fin r),
        (∀ j ∈ L, t' j ∈ IsLocalRing.maximalIdeal R) →
        IsRegularLocalRing (RingTheory.transverseRootCoefficientRing t' L) ∧
          ringKrullDim (RingTheory.transverseRootCoefficientRing t' L) +
            (L.card : WithBot ℕ∞) = ringKrullDim R := by
      intro L hL
      have hLp : ∀ j ∈ L, t j ∈ p := fun j hj ↦
        (IsLocalization.AtPrime.to_map_mem_maximal_iff R p (t j)).mp (hL j hj)
      exact ⟨((hlocal p).1 L hLp).1, ((hlocal p).1 L hLp).2.1⟩
    have hJp : ∀ j ∈ J', t' j ∈ IsLocalRing.maximalIdeal R := by
      intro j hj
      apply (IsLocalization.AtPrime.to_map_mem_maximal_iff R p (t j)).mpr
      change algebraMap A E (t j) ∈ q
      have hz := face_parameter t n hn (J' : Set (Fin r)) j hj
      change algebraMap A E (t j) = 0 at hz
      rw [hz]
      exact q.zero_mem
    have hnR : IsUnit (n : R) := by
      simpa only [map_natCast] using hnunit.map (algebraMap A R)
    have hb := (RingTheory.isRegularRing_transverseLocalRootFamily R (Fin r) t' hs
      n hn hnR J' (Finset.univ \ J') hJp (Finset.disjoint_sdiff)).1
    have hloc := localized_face_regular t n hn J' p hb
    apply regular_at_of_localization q
      (p.primeCompl.map (algebraMap A E)) ?_ hloc
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hqmem
    exact ha hqmem
  let := hE
  let e := DoubleQuot.quotQuotEquivQuotSup (rootIdeal t n)
    (Ideal.span ((fun j : Fin r ↦ (MvPolynomial.X j : MvPolynomial (Fin r) A)) '' J))
  have hface : rootIdeal t n ⊔ Ideal.span (MvPolynomial.X '' J) =
      faceIdeal t n (J' : Set (Fin r)) := by rw [hJ']
  exact IsRegularRing.of_ringEquiv
    ((Ideal.quotEquivOfEq hface).symm.trans e.symm)

end AlgebraicGeometry
