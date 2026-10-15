/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.RingTheory.WeakEtaleRefinement
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso
import Sheaf.RingTheory.RetainedLocalizationProperties
import Sheaf.RingTheory.StrictWCoverProperties
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale

/-! # Properties of the canonical weakly etale refinement

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1232;
Stacks Project, Tag 097Z (blueprint: thm-weil-pbc-weak-etale-refinement).
-/

@[expose] public section

universe u

namespace PrincipalWLocalization.WeakEtaleRefinement

private theorem indEtale_of_principal (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (h : Algebra.IsIndPrincipalZariski R S) : Algebra.IndEtale R S := by
  obtain ⟨I, hcat, hfilt, P, hP⟩ := h
  refine ⟨I, hcat, hfilt, P, fun i ↦ ?_⟩
  obtain ⟨n, f, ⟨e⟩⟩ := hP i
  have (j : Fin n) : Algebra.Etale R (Localization.Away (f j)) :=
    Algebra.Etale.of_isLocalizationAway (f j)
  exact Algebra.Etale.of_equiv e.symm

/-- For the specified refinement, `B → B'` is faithfully flat and ind-etale, and
`A → B'` is ind-etale. The latter map is the composite through `B`.
Source: blueprint order 1232; Stacks Project, Tag 097Z
(blueprint: thm-weil-pbc-weak-etale-refinement).

Proof:
1. Write `C = C_A`, `D₀ = B ⊗[A] C`, and `T = V(JD₀)`. The strict-cover
   properties identify `V(J)` with the closed points of `Spec C`. Weak-etale
   base change and the existing residue-field algebraicity theorem imply that
   `T` consists of closed points. Apply the retained-localization properties.
2. A filtered presentation by finite products of principal localizations is an
   ind-etale presentation: each localization and its finite product are etale.
   Hence `D₀ → B'` is ind-etale. Base change from `A → C` and composition give
   ind-etaleness of `B → B'`, and therefore its flatness.
3. The retained closed-point homeomorphism sends `x` to the pair `(x,x)`.
   Consequently every maximal ideal of `B'` contracts to a maximal ideal of `C`.
   The map `C → B'` is weakly etale. The existing theorem
   `Algebra.WeaklyEtale.bijectiveOnStalks` applies the strictly henselian local
   isomorphism theorem at maximal ideals and localizes again at smaller primes.
   Apply the local-ring criterion for principal ind-Zariski algebras, then step 2.
   Composition with `A → C`, and the tensor balancing identity, give the stated
   ind-etaleness of the composite through `B`.
4. Closed-point surjectivity for `C → A` gives spectrum surjectivity for
   `C/J → A`. Its base change `B ⊗[A] (C/J) → B` is surjective on spectra.
   Contract a prime along `D₀ → B ⊗[A] (C/J)` to get `Q ∈ T`, and lift the
   pair `(Q,Q)` through the retained prime equivalence. This proves spectrum
   surjectivity for `B' → B`. Together with flatness from step 2 it gives
   faithful flatness. No faithful-flatness claim about `D₀ → B'` is needed. -/
theorem properties (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hweak : Algebra.WeaklyEtale A B) :
    (algebraMap B (algebra A B hweak)).FaithfullyFlat ∧
    (algebraMap B (algebra A B hweak)).IndEtale ∧
    ((algebraMap B (algebra A B hweak)).comp (algebraMap A B)).IndEtale :=
    open scoped TensorProduct in by
  classical
  -- Fix the actual maps on the specified tensor product and refinement.
  let C := StrictWCover.algebra A
  let D₀ := tensor A B
  let D := algebra A B hweak
  have : Algebra.WeaklyEtale A B := hweak
  obtain ⟨_, hCind, hCw, hCstrict, hCsurj⟩ := StrictWCover.properties A
  have : Algebra.IndEtale A C := hCind
  have : IsWLocalRing C := hCw
  let : Algebra C D₀ := Algebra.TensorProduct.rightAlgebra
  let : Algebra D₀ D := (tensorToRefinement A B).toAlgebra
  let : Algebra C D := coverAlgebra A B hweak
  have : IsScalarTower C D₀ D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B D₀ D := IsScalarTower.of_algebraMap_eq' rfl
  have hJ : PrimeSpectrum.zeroLocus (closedIdeal A : Set C) =
      closedPoints (PrimeSpectrum C) := by
    exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans
      WLocalSpace.isClosed_closedPoints.closure_eq
  let T : Set (PrimeSpectrum D₀) :=
    PrimeSpectrum.zeroLocus (extendedIdeal A B : Set D₀)
  have hD₀weak : Algebra.WeaklyEtale C D₀ := by
    let e : (TensorProduct A C B) ≃ₐ[C] D₀ := Algebra.TensorProduct.commRight A C B
    let : Algebra (TensorProduct A C B) D₀ := e.toRingHom.toAlgebra
    have : IsScalarTower C (TensorProduct A C B) D₀ :=
      IsScalarTower.of_algebraMap_eq fun c ↦ (e.commutes c).symm
    have : Algebra.Etale (TensorProduct A C B) D₀ :=
      (RingHom.Etale.of_bijective e.bijective).toAlgebra
    exact Algebra.WeaklyEtale.trans C (TensorProduct A C B) D₀
  have hT : ∀ x ∈ T, IsClosed ({x} : Set (PrimeSpectrum D₀)) := by
    have : Algebra.WeaklyEtale C D₀ := hD₀weak
    exact fun x hx ↦ mem_closedPoints_iff.mp
      (zeroLocus_map_algebraMap_subset_closedPoints
        (fun m q _ hm _ _ _ ↦ by
          have : m.IsPrime := hm.isPrime
          exact Algebra.WeaklyEtale.isAlgebraic_residueField_of_liesOver m q)
        hJ.le hx)
  obtain ⟨hret, ⟨e, helocal, heclosed⟩, _⟩ :=
    Retained.properties T (PrimeSpectrum.isClosed_zeroLocus _)
  have hD₀ind : (tensorToRefinement A B).IndEtale :=
    indEtale_of_principal D₀ D hret
  have hB₀ind : (algebraMap B D₀).IndEtale :=
    RingHom.IndEtale.isStableUnderBaseChange A C B D₀
      ((RingHom.IndEtale.algebraMap_iff A C).mpr hCind)
  have hBind : (algebraMap B D).IndEtale := hD₀ind.comp hB₀ind
  have hDweak : Algebra.WeaklyEtale C D := by
    have : Algebra.WeaklyEtale C D₀ := hD₀weak
    have : Algebra.WeaklyEtale D₀ D := hD₀ind.weaklyEtale
    exact Algebra.WeaklyEtale.trans C D₀ D
  obtain ⟨hDw, h, hh⟩ := heclosed hT
  have : IsWLocalRing D := hDw
  -- Retained closed points lie over maximal ideals of the strict cover.
  have hmax : ∀ (n : Ideal D) [n.IsMaximal],
      (n.comap (algebraMap C D)).IsMaximal := by
    intro n hn
    have hnclosed : (⟨n, hn.isPrime⟩ : PrimeSpectrum D) ∈
        closedPoints (PrimeSpectrum D) :=
      mem_closedPoints_iff.mpr ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hn)
    let : TopologicalSpace T :=
      TopologicalSpace.induced Subtype.val (constructibleTopology (PrimeSpectrum D₀))
    obtain ⟨x, hx⟩ := h.toEquiv.surjective ⟨⟨n, hn.isPrime⟩, hnclosed⟩
    change h x = _ at hx
    have hex := hh x
    rw [hx] at hex
    obtain ⟨hncomap, _⟩ := helocal ⟨n, hn.isPrime⟩
    have hxcomap : x.val.asIdeal = n.comap (tensorToRefinement A B) := by
      exact (congrArg (fun p : PrimeSpectrum D₀ × PrimeSpectrum D₀ ↦ p.2.asIdeal)
        hex.symm).trans hncomap
    have hxJ : closedIdeal A ≤ x.val.asIdeal.comap (coverToTensor A B) :=
      Ideal.map_le_iff_le_comap.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp x.property)
    have hxclosed : PrimeSpectrum.comap (coverToTensor A B) x.val ∈
        closedPoints (PrimeSpectrum C) := hJ ▸ hxJ
    change (n.comap ((tensorToRefinement A B).comp (coverToTensor A B))).IsMaximal
    rw [← Ideal.comap_comap, ← hxcomap]
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
      (mem_closedPoints_iff.mp hxclosed)
  -- Strict henselianity identifies all stalks, including at nonmaximal primes.
  have hlocal : Algebra.BijectiveOnStalks C D := by
    have : Algebra.WeaklyEtale C D := hDweak
    apply Algebra.WeaklyEtale.bijectiveOnStalks
    intro q hq
    obtain ⟨n, hn, hqn⟩ := q.exists_le_maximal hq.ne_top
    have : n.IsMaximal := hn
    have : (n.comap (algebraMap C D)).IsMaximal := hmax n
    exact ⟨n, hn.isPrime, hqn, hCstrict _⟩
  have hCprinc : Algebra.IsIndPrincipalZariski C D :=
    Algebra.isIndPrincipalZariski_of_bijective_localRingHom C D
      hlocal.bijective_localRingHom
  have hCDind : (algebraMap C D).IndEtale :=
    (RingHom.IndEtale.algebraMap_iff C D).mpr (indEtale_of_principal C D hCprinc)
  have hcomm : (algebraMap C D).comp (algebraMap A C) =
      (algebraMap B D).comp (algebraMap A B) := by
    ext a
    change tensorToRefinement A B (1 ⊗ₜ[A] algebraMap A C a) =
      tensorToRefinement A B (algebraMap A B a ⊗ₜ[A] 1)
    congr 1
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul a |>.symm
  have hAind : ((algebraMap B D).comp (algebraMap A B)).IndEtale := by
    rw [← hcomm]
    exact hCDind.comp ((RingHom.IndEtale.algebraMap_iff A C).mpr hCind)
  -- Retain a point above every prime of B by first passing to C/J.
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap B D)) := by
    have hCquot : Function.Surjective
        (PrimeSpectrum.comap (algebraMap A (C ⧸ closedIdeal A))) := by
      intro p
      obtain ⟨x, hx⟩ := hCsurj p
      have hxJ : x.val ∈ PrimeSpectrum.zeroLocus (closedIdeal A : Set C) :=
        hJ.symm ▸ x.property
      have hxrange : x.val ∈ Set.range
          (PrimeSpectrum.comap (Ideal.Quotient.mk (closedIdeal A))) := by
        rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
          Ideal.mk_ker]
        exact hxJ
      obtain ⟨x', hx'⟩ := hxrange
      refine ⟨x', ?_⟩
      rw [IsScalarTower.algebraMap_eq A C (C ⧸ closedIdeal A),
        PrimeSpectrum.comap_comp_apply]
      exact (congrArg (PrimeSpectrum.comap (algebraMap A C)) hx').trans hx
    intro q
    obtain ⟨Q₀, hQ₀⟩ := PrimeSpectrum.comap_surjective_tensorProduct_left B hCquot q
    let π : D₀ →ₐ[A] TensorProduct A B (C ⧸ closedIdeal A) :=
      Algebra.TensorProduct.map (AlgHom.id A B) (Ideal.Quotient.mkₐ A (closedIdeal A))
    let Q : PrimeSpectrum D₀ := PrimeSpectrum.comap π.toRingHom Q₀
    have hQT : Q ∈ T := by
      change (closedIdeal A).map (coverToTensor A B) ≤ Q.asIdeal
      rw [Ideal.map_le_iff_le_comap]
      intro c hc
      change π (1 ⊗ₜ[A] c) ∈ Q₀.asIdeal
      rw [Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr hc, TensorProduct.tmul_zero]
      exact Q₀.asIdeal.zero_mem
    have hQq : PrimeSpectrum.comap (algebraMap B D₀) Q = q := by
      have hπ : π.toRingHom.comp (algebraMap B D₀) =
          algebraMap B (TensorProduct A B (C ⧸ closedIdeal A)) := by
        ext b
        change π (b ⊗ₜ[A] 1) = b ⊗ₜ[A] 1
        exact (Algebra.TensorProduct.map_tmul _ _ b 1).trans (by simp)
      change PrimeSpectrum.comap (algebraMap B D₀) (PrimeSpectrum.comap π.toRingHom Q₀) = q
      rw [← PrimeSpectrum.comap_comp_apply, hπ, hQ₀]
    let P : PrimeSpectrum D := e.symm ⟨(Q, Q), hQT, le_rfl⟩
    obtain ⟨hP, _⟩ := helocal P
    have hPQ : PrimeSpectrum.comap (tensorToRefinement A B) P = Q := by
      apply PrimeSpectrum.ext
      exact hP.symm.trans
        (congrArg (fun p ↦ p.val.2.asIdeal) (e.apply_symm_apply _))
    refine ⟨P, ?_⟩
    change PrimeSpectrum.comap ((tensorToRefinement A B).comp (algebraMap B D₀)) P = q
    rw [PrimeSpectrum.comap_comp_apply, hPQ, hQq]
  exact ⟨RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
    ⟨hBind.weaklyEtale.flat, hsurj⟩, hBind, hAind⟩

end PrincipalWLocalization.WeakEtaleRefinement
