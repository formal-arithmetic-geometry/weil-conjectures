/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.ProEtale.WContractible

import Mathlib.Topology.Separation.DisjointCover
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RingTheory.StrictlyHenselianQuotient
import WeilConjectures.RingTheory.HenselianPairPrimeConnected
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import WeilConjectures.RingTheory.FactorsThroughLocalization
import Sheaf.RingTheory.WLocalClopenPartitions
import Sheaf.RingTheory.HenselianSmoothAlgebraLifting
import WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian

/-!
# Henselian reduction and w-strict locality

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 2.2.13, with the
local-ring characterization in Lemma 2.2.9
(blueprint: lem-zl-henselian-wstrict-local-invariance).
-/

@[expose] public section

universe u

-- Base change an étale cover to a strictly henselian maximal stalk and take a section.
open PrimeSpectrum Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
open scoped TensorProduct in
private theorem etale_stalk_map (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] [Module.FaithfullyFlat A B]
    (m : Ideal A) [m.IsMaximal]
    [IsStrictlyHenselianLocalRing (Localization.AtPrime m)] :
    Nonempty (B →ₐ[A] Localization.AtPrime m) := by
  let L := Localization.AtPrime m
  let T := L ⊗[A] B
  let j := Spec.map (CommRingCat.ofHom (algebraMap L T))
  have : Etale j := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact (RingHom.etale_algebraMap.mpr inferInstance)
  obtain ⟨y, hy⟩ := (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := L) (B := T))
    (IsLocalRing.closedPoint L)
  obtain ⟨s, hs⟩ :=
    Scheme.exists_section_of_etale_of_isStrictlyHenselianLocalRing j y hy
  let t := (Spec.preimage s).hom
  have ht : t.comp (algebraMap L T) = RingHom.id L := by
    have h := congrArg Spec.preimage hs
    simpa [j, t, Spec.preimage_comp, Spec.preimage_id] using
      congrArg CommRingCat.Hom.hom h
  let r : T →ₐ[L] L := { t with commutes' := fun a ↦ RingHom.congr_fun ht a }
  exact ⟨(r.restrictScalars A).comp Algebra.TensorProduct.includeRight⟩

-- BS Lemma 2.2.9: spread stalk sections and glue on a disjoint clopen refinement.
open PrimeSpectrum Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
open scoped TensorProduct in
private theorem etale_retraction_of_wStrict (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] [Module.FaithfullyFlat A B]
    [IsWStrictlyLocalRing A] : Nonempty (B →ₐ[A] A) := by
  classical
  let C := closedPoints (PrimeSpectrum A)
  have hlocal (c : C) : ∃ f : A, f ∉ c.val.asIdeal ∧
      Nonempty (B →ₐ[A] Localization.Away f) := by
    have : c.val.asIdeal.IsMaximal :=
      (isClosed_singleton_iff_isMaximal c.val).mp (mem_closedPoints_iff.mp c.property)
    have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization c.val.asIdeal
    obtain ⟨g⟩ := etale_stalk_map A B c.val.asIdeal
    obtain ⟨f, g', _, _⟩ := Algebra.factors_through_principal_localization A B A
      c.val.asIdeal.primeCompl g
    exact ⟨f, f.property, ⟨g'⟩⟩
  choose f hf g using hlocal
  let U : C → TopologicalSpace.Opens C := fun c ↦
    (PrimeSpectrum.basicOpen (f c)).comap ⟨Subtype.val, continuous_subtype_val⟩
  have hcover : TopologicalSpace.IsOpenCover U := by
    apply TopologicalSpace.IsOpenCover.mk
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup]
    apply Set.eq_univ_of_forall
    intro c
    exact Set.mem_iUnion.mpr ⟨c, hf c⟩
  obtain ⟨n, P, hP, hPc, hPd⟩ := hcover.exists_finite_nonempty_disjoint_clopen_cover
  have hpart := (PrimeSpectrum.wLocal_clopen_partition_properties A).2
    (inferInstance : IsWLocalRing A)
  obtain ⟨Q, hQ, _⟩ := (hpart.2.1 (Fin n) (fun i ↦ (P i : Set C))).mp
    ⟨fun i ↦ (P i).isClopen, fun i j hij ↦
      TopologicalSpace.Clopens.coe_disjoint.mpr (hPd hij),
      Set.eq_univ_of_univ_subset hPc⟩
  choose c hc using fun i ↦ (hP i).2
  let X := Spec (CommRingCat.of A)
  let O : Fin n → X.Opens := fun i ↦ ⟨Q i, (hQ.1 i).isOpen⟩
  let j (i : Fin n) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (f (c i)))))
  have hle (i : Fin n) : O i ≤ (j i).opensRange := by
    change O i ≤ (Spec.map (CommRingCat.ofHom
      (algebraMap A (Localization.Away (f (c i)))))).opensRange
    rw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A)]
    intro x hx
    obtain ⟨d, hd, hxd⟩ := exists_isClosed_specializes x
    let d' : C := ⟨d, mem_closedPoints_iff.mpr hd⟩
    have hdQ : d ∈ Q i := (hQ.1 i).isClosed.stableUnderSpecialization hxd hx
    have hdP : d' ∈ (P i : Set C) := by
      rw [← hQ.2.2.2 i]
      exact hdQ
    exact hxd.mem_open (PrimeSpectrum.basicOpen (f (c i))).isOpen (hc i hdP)
  have hOc : ⨆ i, O i = ⊤ := by
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    change (⋃ i, Q i) = Set.univ
    exact hQ.2.2.1
  have hOd : Pairwise (fun i j ↦ Disjoint (O i) (O j)) := by
    intro i j hij
    exact TopologicalSpace.Opens.coe_disjoint.mp (hQ.2.1 hij)
  obtain ⟨hX⟩ := nonempty_isColimit_cofanMk_of (fun i ↦ (O i).ι)
    (by simpa using hOc) (by simpa using hOd)
  let t : ∀ i, (O i).toScheme ⟶ Spec (CommRingCat.of B) := fun i ↦
    X.homOfLE (hle i) ≫ (j i).isoOpensRange.inv ≫
      Spec.map (CommRingCat.ofHom (g (c i)).some.toRingHom)
  let s := Cofan.IsColimit.desc hX t
  have hs : s ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = 𝟙 X := by
    apply Cofan.IsColimit.hom_ext hX
    intro i
    rw [← Category.assoc, Cofan.IsColimit.fac hX t i]
    dsimp only [t]
    rw [Category.assoc, Category.assoc, ← Spec.map_comp]
    have he : CommRingCat.ofHom (algebraMap A B) ≫
        CommRingCat.ofHom (g (c i)).some.toRingHom =
        CommRingCat.ofHom (algebraMap A (Localization.Away (f (c i)))) := by
      ext a
      exact (g (c i)).some.commutes a
    rw [he, Scheme.Hom.isoOpensRange_inv_comp]
    exact Scheme.homOfLE_ι _ _
  let r := (Spec.preimage s).hom
  have hr : r.comp (algebraMap A B) = RingHom.id A := by
    have h := congrArg Spec.preimage hs
    simpa [X, r, Spec.preimage_comp, Spec.preimage_id] using
      congrArg CommRingCat.Hom.hom h
  exact ⟨{ r with commutes' := fun a ↦ RingHom.congr_fun hr a }⟩

-- BS Lemma 2.2.13: connectedness of V(p + I) forces unique closed specializations.
open PrimeSpectrum Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
open scoped TensorProduct in
private theorem wLocal_of_henselian_quotient (A : Type u) [CommRing A]
    (I : Ideal A) [HenselianRing A I] [IsWLocalRing (A ⧸ I)] : IsWLocalRing A := by
  classical
  let q := Ideal.Quotient.mk I
  let f := PrimeSpectrum.comap q
  have hf := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (A ⧸ I) q
    Ideal.Quotient.mk_surjective
  have hI (c : PrimeSpectrum A) (hc : IsClosed ({c} : Set (PrimeSpectrum A))) :
      I ≤ c.asIdeal := by
    have : c.asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal c).mp hc
    exact (HenselianRing.jac (R := A) (I := I)).trans (by
      rw [Ideal.jacobson_bot]
      exact Ring.jacobson_le_of_isMaximal c.asIdeal)
  have hrange (c : PrimeSpectrum A) (hc : IsClosed ({c} : Set (PrimeSpectrum A))) :
      c ∈ Set.range f := by
    rw [range_comap_of_surjective (A ⧸ I) q Ideal.Quotient.mk_surjective]
    simpa [q, Ideal.mk_ker, mem_zeroLocus] using hI c hc
  have hclosed : f '' closedPoints (PrimeSpectrum (A ⧸ I)) =
      closedPoints (PrimeSpectrum A) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨c, hc, rfl⟩
      apply mem_closedPoints_iff.mpr
      simpa only [Set.image_singleton] using
        hf.isClosedMap _ (mem_closedPoints_iff.mp hc)
    · intro c hc
      obtain ⟨d, rfl⟩ := hrange c (mem_closedPoints_iff.mp hc)
      exact ⟨d, mem_closedPoints_iff.mpr
        (hf.isEmbedding.isClosed_singleton_of_isClosed_image_singleton
          (mem_closedPoints_iff.mp hc)), rfl⟩
  have hcl : IsClosed (closedPoints (PrimeSpectrum A)) := by
    rw [← hclosed]
    exact hf.isClosedMap _ WLocalSpace.isClosed_closedPoints
  refine ⟨{ isClosed_closedPoints := hcl, eq_of_specializes := ?_ }⟩
  intro x c d hc hd hxc hxd
  obtain ⟨c', rfl⟩ := hrange c hc
  obtain ⟨d', rfl⟩ := hrange d hd
  have : x.asIdeal.IsPrime := x.isPrime
  have hconn := isConnected_iff_connectedSpace.mpr
    (PrimeSpectrum.connectedSpace_zeroLocus_sup_of_henselian I x.asIdeal)
  have himage : f '' zeroLocus (x.asIdeal.map q : Set (A ⧸ I)) =
      zeroLocus ((x.asIdeal ⊔ I : Ideal A) : Set A) := by
    rw [image_comap_zeroLocus_eq_zeroLocus_comap (A ⧸ I) q
      Ideal.Quotient.mk_surjective, Ideal.comap_map_of_surjective q
      Ideal.Quotient.mk_surjective, show Ideal.comap q ⊥ = I from Ideal.mk_ker]
  have hpre : _root_.IsPreconnected (zeroLocus (x.asIdeal.map q : Set (A ⧸ I))) :=
    hf.isEmbedding.isInducing.isPreconnected_image.mp (himage.symm ▸ hconn.isPreconnected)
  have hc' : c' ∈ zeroLocus (x.asIdeal.map q : Set (A ⧸ I)) := by
    rw [mem_zeroLocus]
    exact Ideal.map_le_iff_le_comap.mpr ((le_iff_specializes _ _).mpr hxc)
  have hd' : d' ∈ zeroLocus (x.asIdeal.map q : Set (A ⧸ I)) := by
    rw [mem_zeroLocus]
    exact Ideal.map_le_iff_le_comap.mpr ((le_iff_specializes _ _).mpr hxd)
  apply congrArg f
  apply WLocalSpace.closedPoints_eq_of_mk_eq
    (mem_closedPoints_iff.mpr
      (hf.isEmbedding.isClosed_singleton_of_isClosed_image_singleton hc))
    (mem_closedPoints_iff.mpr
      (hf.isEmbedding.isClosed_singleton_of_isClosed_image_singleton hd))
  exact (hpre.image ConnectedComponents.mk
    ConnectedComponents.continuous_coe.continuousOn).subsingleton
    ⟨c', hc', rfl⟩ ⟨d', hd', rfl⟩

/-- Henselian reduction preserves and reflects w-strict locality.
Source: Bhatt--Scholze, Lemmas 2.2.13, 2.2.9 and 2.2.15
(blueprint: lem-zl-henselian-wstrict-local-invariance).

Proof plan:
1. The henselian factorization criterion puts `I` in the Jacobson radical. The prime-spectrum
   quotient correspondence identifies `Spec (A/I)` with `V(I)` and identifies their closed
   points with those of `Spec A` (lem-weil-pbc-henselian-factorization-criterion,
   def-weil-affine-spectrum).
2. Closedness of the closed-point set and uniqueness of closed specializations descend to
   this closed subspace, giving w-locality of the quotient (sk-def-pe-wlocal).
3. Localizing the quotient at a maximal ideal gives the corresponding quotient of the
   maximal localization. Strict henselianity descends to this proper quotient, giving
   w-strict locality of `A/I` (lem-weil-pbc-localization-at-prime-of-quotient,
   lem-weil-pbc-strictly-henselian-quotient, sk-def-pe-wlocal).
4. Conversely assume `A/I` is w-strictly local. Its closed points are closed also in
   `Spec A`. For every prime `p`, the nonempty connected subset `V(p+I)` maps under the
   closed-point retraction to a singleton in the profinite closed-point space. Its maximal
   ideals are fixed by this retraction, so `p` has a unique maximal specialization. Thus
   `A` is w-local (lem-weil-pbc-henselian-pair-prime-connected, det-pe-wlocal-components,
   sk-def-pe-wlocal).
5. For any faithfully flat etale `A`-algebra `B`, base change gives an etale surjection
   `Spec (B/IB)` to `Spec (A/I)`, using the affine tensor-product identification
   (lem-weil-pbc-faithfully-flat-surjective-spectrum, lem-weil-pbc-etale-covering-base-change,
   lem-weil-pbc-fibre-product-affine-spectra).
6. At each maximal localization of `A/I`, strict henselianity supplies a section of this
   etale surjection, hence an algebra map to that localization
   (lem-weil-pbc-etale-covering-base-change,
   lem-sbc-strict-henselian-etale-neighbourhood-section, sk-def-pe-wlocal,
   def-weil-affine-spectrum).
7. Finite presentation spreads each section to a principal open neighbourhood
   (lem-weil-pbc-etale-ring-map-iff-etale-affine,
   lem-factors-through-localization-of-smooth, def-weil-affine-spectrum).
8. Compactness and profiniteness give a subordinate finite clopen partition of the closed
   points. Extend it to `Spec (A/I)` and glue the sections on disjoint parts to an
   `A/I`-algebra map `B/IB` to `A/I` (lem-weil-pbc-w-local-partition,
   def-weil-affine-spectrum, det-pe-wlocal-components).
9. Etale implies smooth: the cotangent module and first cotangent homology vanish.
   Henselian smooth-algebra lifting lifts the resulting map `B` to `A/I` to an
   `A`-algebra map `B` to `A`, hence a retraction of the structure map
   (lem-weil-pbc-etale-ring-map-iff-etale-affine, def-weil-pbc-smooth-ring-map,
   lem-trf-henselian-smooth-algebra-lifting; Stacks Tag 0H74).
10. Every faithfully flat etale `A`-algebra therefore splits. The maximal-local criterion
    gives strictly henselian maximal localizations. Combined with step 4 this proves
    w-strict locality of `A` (lem-weil-pbc-split-etale-covers-maximal-local-criterion,
    sk-def-pe-wlocal; Stacks Tag 097V). -/
theorem isWStrictlyLocalRing_iff_quotient_of_henselianRing
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I] :
    IsWStrictlyLocalRing A ↔ IsWStrictlyLocalRing (A ⧸ I) := by
  constructor
  · intro hA
    let : IsWStrictlyLocalRing A := hA
    have : IsWLocalRing (A ⧸ I) :=
      IsWLocalRing.of_surjective (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    refine { isStrictlyHenselianLocalRing_localization := ?_ }
    intro m hm
    let p := m.comap (Ideal.Quotient.mk I)
    have : p.IsMaximal := Ideal.comap_isMaximal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    let S := Localization.AtPrime p
    let J := I.map (algebraMap A S)
    have hS := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization p
    have hJ : J ≤ IsLocalRing.maximalIdeal S := by
      apply Ideal.map_le_iff_le_comap.mpr
      change I ≤ (IsLocalRing.maximalIdeal S).under A
      rw [IsLocalization.AtPrime.under_maximalIdeal S p]
      intro a ha
      change Ideal.Quotient.mk I a ∈ m
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact m.zero_mem
    obtain ⟨_, _, _, hstrict, _⟩ := isStrictlyHenselianLocalRing_quotient.{u, u} S hS J hJ
    let : IsStrictlyHenselianLocalRing (S ⧸ J) := hstrict
    have hmon : Algebra.algebraMapSubmonoid (A ⧸ I) p.primeCompl = m.primeCompl :=
      Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective m
    have : IsLocalization m.primeCompl (S ⧸ J) := by
      rw [← hmon]
      infer_instance
    exact IsStrictlyHenselianLocalRing.of_ringEquiv
      (IsLocalization.algEquiv m.primeCompl (S ⧸ J) (Localization.AtPrime m)).toRingEquiv
  · intro hR
    let : IsWStrictlyLocalRing (A ⧸ I) := hR
    have := wLocal_of_henselian_quotient A I
    refine { isStrictlyHenselianLocalRing_localization := ?_ }
    intro m hm
    apply IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction
    intro B _ _ hB hsurj
    let : Algebra.Etale A B := hB
    have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_comap_surjective hsurj
    obtain ⟨r⟩ := etale_retraction_of_wStrict (A ⧸ I) (TensorProduct A (A ⧸ I) B)
    let σ : B →ₐ[A] A ⧸ I := (r.restrictScalars A).comp Algebra.TensorProduct.includeRight
    obtain ⟨ρ, _⟩ := Algebra.Smooth.exists_lift_of_henselianRing A B A I σ
    exact ⟨ρ.toRingHom, by ext a; exact ρ.commutes a⟩
