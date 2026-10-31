/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.SNCRootLocalPresentation
import WeilConjectures.RingTheory.TransverseLocalRootFamilyRegular
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Regularity of finite simultaneous roots along strict normal crossings

Source: ILO, Travaux de Gabber, Expose IX, Proposition 2.1 proof, printed p.133;
Stacks Project, Tag 0BIA, `lemma-strict-normal-crossings`.
(blueprint: lem-sfb-snc-finite-root-regular-ring).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- Adjoining simultaneous roots of the distinct reduced branches of an SNC boundary
on a regular affine scheme gives a regular Noetherian ring. The equations define reduced
closed subschemes, their zero loci are distinct, and these zero loci are precisely all
irreducible components of the boundary. No nontriviality assumption is imposed.

Source: ILO IX, Proposition 2.1 proof, printed p.133; Stacks Tag 0BIA.
(blueprint: lem-sfb-snc-finite-root-regular-ring).

Proof:
1. Local Noetherianity of the regular scheme gives Noetherianity of A by
   `pqf-lem-affine-open-locnoeth`. The finite polynomial quotient is Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`. The zero ring has no primes.
   For a prime q of the quotient, contract to p in A and identify the stalk with A_p
   using `lem-weil-pbc-affine-open-stalk-localization`.
2. Let S index the equations in p. For J contained in S put R_J = A_p/(t_j : j in J).
   The SNC regular-intersection condition, the stalk identification, and
   `lem-weil-pbc-localization-at-prime-of-quotient` make each R_J regular local with
   dim(R_J) + card(J) = dim(A_p). Equations not in S are units in all these rings.
3. For J contained in S and K disjoint from J, form B_{J,K} by adjoining the roots
   indexed by K over R_J. Iterating `lem-weil-pbc-monic-quotient-free` gives the finite
   free monomial basis with exponents less than n. The presentations can be reordered
   by maps fixing their generators. Induct simultaneously over J on card(K).
   The empty K case follows from `lem-weil-pbc-regular-local-localization`.
4. Choose i in K and set D = B_{J,K\{i}}, B = D[T]/(T^n-t_i), with root u.
   The induction makes D regular. At a prime Q containing u, i belongs to S.
   The dimension equalities show t_i is nonzero in R_J; this regular local ring is a
   domain by `lem-sc-regular-local-domain`, so t_i acts injectively on the free D.
5. Quotienting D by t_i gives B_{J union {i},K\{i}}: the two maps fix coefficients
   modulo t_i and the remaining roots, and their composites fix all generators.
   The induction makes this quotient regular. Apply
   `lem-sbc-root-algebra-regular-at-root` to obtain regularity of B_Q.
6. At a prime Q missing u, t_i is also outside Q. The ring E = D[1/t_i] is regular
   by `lem-weil-pbc-localization-of-regular-ring`, and E[T] is regular by
   `lem-trf-polynomial-ring-regular-base`. In E[T]/(T^n-t_i), T is invertible with
   inverse T^(n-1)/t_i. Thus the derivative n*T^(n-1) is a unit, and
   `lem-weil-pbc-hypersurface-derivation-regular` gives regularity of this quotient.
   Its localization at the extended prime is B_Q, since t_i is already invertible
   there. This completes the induction.
7. Take J empty and K all indices. Localization of the displayed presentation
   from A to A_p commutes with the quotient: mutually inverse maps fix coefficients
   and roots. Localizing further at q gives exactly the original prime localization.
   Thus every prime localization is regular local. For r = 0 the polynomial ring
   in no variables and its quotient by the empty relation ideal identify with A;
   this is the induction base. The argument also includes n = 1.
-/
theorem isRegularRing_snc_finiteRoot
    (A : Type u) [CommRing A] (hA : IsRegularScheme (Spec (.of A)))
    (r : ℕ) (t : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hreduced : ∀ i : Fin r, _root_.IsReduced (A ⧸ Ideal.span ({t i} : Set A)))
    (hdistinct : Function.Injective
      (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : A)) :
    IsRegularRing (MvPolynomial (Fin r) A ⧸
      Ideal.span (Set.range (fun i : Fin r ↦
        (MvPolynomial.X i : MvPolynomial (Fin r) A) ^ n - MvPolynomial.C (t i)))) := by
  classical
  have hex (i : Fin r) : ∃ Z ∈ irreducibleComponents (H.support :
      Set (Spec (.of A))), Subtype.val '' Z = PrimeSpectrum.zeroLocus {t i} := by
    have hi := Set.mem_range_self (f := fun i : Fin r ↦
      PrimeSpectrum.zeroLocus ({t i} : Set A)) i
    rw [hbranches] at hi
    exact hi
  choose c hc heq using hex
  let f : Fin r → {Z : Set (H.support : Set (Spec (.of A))) //
      Z ∈ irreducibleComponents (H.support : Set (Spec (.of A)))} :=
    fun i ↦ ⟨c i, hc i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply hdistinct
      exact (heq i).symm.trans ((congrArg (fun Z ↦ Subtype.val '' Z.val) hij).trans (heq j))
    · intro Z
      have hZ : Subtype.val '' Z.val ∈ Set.range
          (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) := by
        rw [hbranches]
        exact ⟨Z.val, Z.property, rfl⟩
      obtain ⟨i, hi⟩ := hZ
      refine ⟨i, Subtype.ext ?_⟩
      exact Subtype.val_injective.image_injective ((heq i).trans hi)
  let components := Equiv.ofBijective f hf
  have hcomponent (i : Fin r) : Subtype.val '' (components i).val =
      PrimeSpectrum.zeroLocus ({t i} : Set A) := heq i
  have hbranches' (i : Fin r) : (Ideal.span {t i}).IsPrime ∧
      Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t i})))) =
        Subtype.val '' (components i).val := by
    constructor
    · apply (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _
        ((Ideal.isRadical_iff_quotient_reduced _).mpr (hreduced i))).mp
      rw [PrimeSpectrum.zeroLocus_span, ← hcomponent]
      exact (components i).property.prop.image _ continuous_subtype_val.continuousOn
    · rw [hcomponent]
      change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {t i}))) = _
      rw [range_comap_of_surjective _ (Ideal.Quotient.mk (Ideal.span {t i}))
          Ideal.Quotient.mk_surjective,
        Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
  obtain ⟨hnoeth, hrootNoeth, hlocal⟩ :=
    snc_root_local_presentation A hA r t H hH components hbranches' n hn
  let := hnoeth
  let := hrootNoeth
  rw [isRegularRing_iff]
  intro q hq
  let p : Ideal A := q.comap (algebraMap A _)
  have : p.IsPrime := Ideal.comap_isPrime _ q
  obtain ⟨hstrata, e, he, -⟩ := hlocal p
  obtain ⟨Q, hQ, -, eq, -⟩ := he.2.2 q rfl
  have := hQ
  let R := Localization.AtPrime p
  let t' : Fin r → R := fun i ↦ algebraMap A R (t i)
  have : IsRegularLocalRing R := by
    let := hA.2
    exact IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (.of A) ⟨p, inferInstance⟩).commRingCatIsoToRingEquiv
  have hstrata' (J : Finset (Fin r))
      (hJ : ∀ j ∈ J, t' j ∈ IsLocalRing.maximalIdeal R) :
      IsRegularLocalRing (RingTheory.transverseRootCoefficientRing t' J) ∧
        ringKrullDim (RingTheory.transverseRootCoefficientRing t' J) +
          (J.card : WithBot ℕ∞) = ringKrullDim R := by
    have hJ' : ∀ j ∈ J, t j ∈ p := fun j hj ↦
      (IsLocalization.AtPrime.to_map_mem_maximal_iff R p (t j)).mp (hJ j hj)
    exact ⟨(hstrata J hJ').1, (hstrata J hJ').2.1⟩
  have hnunit' : IsUnit (n : R) := by
    simpa only [map_natCast] using hnunit.map (algebraMap A R)
  have hregular := (RingTheory.isRegularRing_transverseLocalRootFamily R (Fin r) t'
    hstrata' n hn hnunit' ∅ Finset.univ (by simp) (by simp)).1
  have hB : IsRegularRing (MvPolynomial (Fin r) R ⧸
      Ideal.span (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n -
        MvPolynomial.C (t' i)))) := by
    let eR : RingTheory.transverseRootCoefficientRing t' ∅ ≃+* R :=
      (Ideal.quotEquivOfEq (show Ideal.span (t' '' (↑(∅ : Finset (Fin r)) :
        Set (Fin r))) = ⊥ by simp)).trans (RingEquiv.quotientBot R)
    have heR (a : R) : eR (Ideal.Quotient.mk _ a) = a := by
      simp [eR]
    let eI : (Finset.univ : Finset (Fin r)) ≃ Fin r :=
      Equiv.ofBijective (fun i ↦ i.val)
        ⟨Subtype.val_injective, fun i ↦ ⟨⟨i, Finset.mem_univ i⟩, rfl⟩⟩
    let eP := (MvPolynomial.mapEquiv _ eR).trans
      (MvPolynomial.renameEquiv R eI).toRingEquiv
    have hgen (i : (Finset.univ : Finset (Fin r))) :
        eP (MvPolynomial.X i ^ n -
          MvPolynomial.C (Ideal.Quotient.mk _ (t' i))) =
          MvPolynomial.X (i : Fin r) ^ n - MvPolynomial.C (t' i) := by
      simp [eP, heR, eI]
    have hrel : Ideal.span (Set.range (fun i : Fin r ↦ MvPolynomial.X i ^ n -
        MvPolynomial.C (t' i))) =
        (RingTheory.transverseRootRelationIdeal t' n ∅ Finset.univ).map eP := by
      rw [RingTheory.transverseRootRelationIdeal, Ideal.map_span, ← Set.range_comp]
      congr 1
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨⟨i, Finset.mem_univ i⟩, hgen _⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, (hgen i).symm⟩
    let := hregular
    exact IsRegularRing.of_ringEquiv (Ideal.quotientEquiv _ _ eP hrel)
  let := hB
  exact IsRegularLocalRing.of_ringEquiv eq

end AlgebraicGeometry
