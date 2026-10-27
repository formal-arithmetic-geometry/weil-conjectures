/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.Topology.FilteredSpectrumTopologicalLimit

/-!
# Topology of directed limits of w-local affine spectra

Source: Bhatt–Scholze, Lemma 2.1.9 (cofiltered-limit paragraph), Lemma 2.1.4 and
Remark 2.1.5 (blueprint: lem-sfb-wlocal-directed-limit-topology).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace PrimeSpectrum

/-- The maximal specializations, closed-point locus and two canonical topological comparisons
for a directed colimit of w-local rings whose transition maps preserve maximal ideals.
Here `PrimeSpectrum` is the underlying Zariski space of `AlgebraicGeometry.Spec`;
`closedPoints` has the subspace topology and `ConnectedComponents` the quotient topology.
The compatible families in the two conclusions have the subspace topology of the product.

Source: Bhatt–Scholze, Lemma 2.1.9, cofiltered-limit paragraph, with Lemma 2.1.4 and
Remark 2.1.5 (blueprint: lem-sfb-wlocal-directed-limit-topology).

Proof for stage 3:
1. Apply `lem-a1-filtered-spectrum-topological-limit` to identify the colimit spectrum
with compatible prime families, with its coordinate topology. Affine spectra are qcqs
by `lem-weil-pbc-affine-scheme-qcqs`, hence spectral by
`lem-weil-pbc-qcqs-scheme-spectral`. Coordinate maps are continuous.
2. In a spectrum, specialization is inclusion of prime ideals. Closure of a singleton
in a product is the product of the coordinate closures, and closure in a subspace is
its intersection with the ambient closure. The prime-family homeomorphism therefore
detects both inclusion and equality of primes by their contractions.
3. For a prime p of the colimit, let m_d be the unique maximal ideal containing its
contraction p_d, using `sk-def-pe-wlocal`. Contraction of m_e along a transition is
maximal by hypothesis and contains p_d, so uniqueness makes the m_d compatible.
4. The prime-family bijection gives a prime m with these maximal contractions, and
coordinatewise inclusion gives p ≤ m.
5. For any prime q containing p, choose a maximal ideal above each contraction q_d
by `lem-weil-pbc-proper-ideal-contained-in-maximal`. It must equal m_d by uniqueness
above p_d, so q ≤ m. Choose a maximal ideal above m by the same theorem; it equals m.
Thus m is maximal and every maximal ideal above p equals m. Its contractions are m_d.
6. A maximal p equals its m, hence has maximal contractions. Conversely, if all p_d
are maximal, they equal m_d, so the prime-family bijection gives p = m, which is maximal.
7. Closed points of a spectrum are maximal ideals. Step 6 identifies the closed-point
locus with the intersection of the inverse images of the stage closed-point loci.
This intersection is closed by continuity and stage w-locality. Spectrality and the
unique closed specialization from step 5 give w-locality of the colimit.
8. Restrict the prime-family homeomorphism to closed points. Step 6 identifies its
image with compatible closed-point families. Product subspace topologies agree:
basic opens on both sides impose finitely many coordinate-open conditions.
9. Apply `det-pe-wlocal-components`, clause 2, at the stages and colimit. The component
quotient restricts to a homeomorphism from closed points to components. Steps 3–5 show
that contraction commutes with the unique closed specialization, hence with these
homeomorphisms, for both coprojections and transition maps.
10. The coordinatewise closed-point/component homeomorphisms on products restrict
to compatible-family subspaces by step 9. Compose with step 8 and the inverse
closed-point/component homeomorphism of the colimit. Its value on the component of x
is the family of components of its contractions. No injectivity or nonempty spectrum
is used; the empty colimit spectrum gives empty compatible-family spaces as well. -/
theorem wLocal_directedLimit_topology
    (D : Type u) [PartialOrder D] [Nonempty D]
    (hdir : Directed (· ≤ ·) (id : D → D))
    (F : D ⥤ CommRingCat.{u})
    (hw : ∀ d : D, IsWLocalRing (F.obj d))
    (hmax : ∀ (d e : D) (hde : d ≤ e) (n : Ideal (F.obj e)),
      n.IsMaximal → (n.comap (F.map (homOfLE hde)).hom).IsMaximal)
    (c : Cocone F) (hc : IsColimit c) :
    (∀ p : PrimeSpectrum c.pt, ∃ m : Ideal c.pt,
      m.IsMaximal ∧ p.asIdeal ≤ m ∧
      (∀ n : Ideal c.pt, n.IsMaximal → p.asIdeal ≤ n → n = m) ∧
      ∀ d : D,
        (m.comap (c.ι.app d).hom).IsMaximal ∧
        p.asIdeal.comap (c.ι.app d).hom ≤ m.comap (c.ι.app d).hom ∧
        ∀ n : Ideal (F.obj d), n.IsMaximal →
          p.asIdeal.comap (c.ι.app d).hom ≤ n → n = m.comap (c.ι.app d).hom) ∧
    (∀ p : PrimeSpectrum c.pt,
      p.asIdeal.IsMaximal ↔
        ∀ d : D, (p.asIdeal.comap (c.ι.app d).hom).IsMaximal) ∧
    (closedPoints (PrimeSpectrum c.pt) =
      ⋂ d : D, (PrimeSpectrum.comap (c.ι.app d).hom) ⁻¹'
        closedPoints (PrimeSpectrum (F.obj d))) ∧
    IsWLocalRing c.pt ∧
    (∃ e : closedPoints (PrimeSpectrum c.pt) ≃ₜ
        {p : (d : D) → closedPoints (PrimeSpectrum (F.obj d)) //
          ∀ (d e : D) (hde : d ≤ e),
            PrimeSpectrum.comap (F.map (homOfLE hde)).hom (p e).val = (p d).val},
      ∀ (m : closedPoints (PrimeSpectrum c.pt)) (d : D),
        ((e m).val d).val = PrimeSpectrum.comap (c.ι.app d).hom m.val) ∧
    (∃ e : ConnectedComponents (PrimeSpectrum c.pt) ≃ₜ
        {p : (d : D) → ConnectedComponents (PrimeSpectrum (F.obj d)) //
          ∀ (d e : D) (hde : d ≤ e),
            (PrimeSpectrum.continuous_comap (F.map (homOfLE hde)).hom).connectedComponentsMap
              (p e) = p d},
      ∀ (x : PrimeSpectrum c.pt) (d : D),
        (e (ConnectedComponents.mk x)).val d =
          ConnectedComponents.mk (PrimeSpectrum.comap (c.ι.app d).hom x)) := by
  classical
  have (d : D) : IsWLocalRing (F.obj d) := hw d
  obtain ⟨E, hE⟩ :=
    (AlgebraicGeometry.filteredSpectrumTopologicalLimit D hdir F c hc).1
  have hcoord (p : PrimeSpectrum c.pt) (d : D) :
      (E p).val d = PrimeSpectrum.comap (c.ι.app d).hom p :=
    congrFun (hE p) d
  have hinj {p q : PrimeSpectrum c.pt}
      (h : ∀ d, PrimeSpectrum.comap (c.ι.app d).hom p =
        PrimeSpectrum.comap (c.ι.app d).hom q) : p = q := by
    apply E.injective
    apply Subtype.ext
    funext d
    rw [hcoord, hcoord, h d]
  have hle {p q : PrimeSpectrum c.pt}
      (h : ∀ d, (PrimeSpectrum.comap (c.ι.app d).hom p).asIdeal ≤
        (PrimeSpectrum.comap (c.ι.app d).hom q).asIdeal) : p.asIdeal ≤ q.asIdeal := by
    apply (PrimeSpectrum.le_iff_specializes p q).mpr
    apply E.isEmbedding.specializes_iff.mp
    apply (subtype_specializes_iff _ _).mpr
    apply specializes_pi.mpr
    intro d
    rw [hcoord, hcoord]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp (h d)
  have hstage (d : D) (p : PrimeSpectrum (F.obj d)) :
      ∃! m : PrimeSpectrum (F.obj d), m.asIdeal.IsMaximal ∧ p.asIdeal ≤ m.asIdeal := by
    obtain ⟨m, hm, hpm⟩ := exists_isClosed_specializes p
    refine ⟨m, ⟨(isClosed_singleton_iff_isMaximal m).mp hm,
      (le_iff_specializes p m).mpr hpm⟩, ?_⟩
    intro n hn
    exact WLocalSpace.eq_of_specializes
      ((isClosed_singleton_iff_isMaximal n).mpr hn.1) hm
      ((le_iff_specializes p n).mp hn.2) hpm
  have hmax_of_coords (p : PrimeSpectrum c.pt)
      (hp : ∀ d, (p.asIdeal.comap (c.ι.app d).hom).IsMaximal) :
      p.asIdeal.IsMaximal := by
    obtain ⟨n, hn, hpn⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
    let q : PrimeSpectrum c.pt := ⟨n, hn.isPrime⟩
    have hpq : p = q := hinj fun d ↦ by
      apply PrimeSpectrum.ext
      exact (hp d).eq_of_le (q.isPrime.comap _).ne_top (Ideal.comap_mono hpn)
    exact hpq ▸ hn
  have hfirst (p : PrimeSpectrum c.pt) : ∃ m : Ideal c.pt,
      m.IsMaximal ∧ p.asIdeal ≤ m ∧
      (∀ n : Ideal c.pt, n.IsMaximal → p.asIdeal ≤ n → n = m) ∧
      ∀ d : D,
        (m.comap (c.ι.app d).hom).IsMaximal ∧
        p.asIdeal.comap (c.ι.app d).hom ≤ m.comap (c.ι.app d).hom ∧
        ∀ n : Ideal (F.obj d), n.IsMaximal →
          p.asIdeal.comap (c.ι.app d).hom ≤ n → n = m.comap (c.ι.app d).hom := by
    choose m hm huniq using fun d ↦ hstage d (PrimeSpectrum.comap (c.ι.app d).hom p)
    have hcompat (d e : D) (hde : d ≤ e) :
        PrimeSpectrum.comap (F.map (homOfLE hde)).hom (m e) = m d := by
      apply huniq d
      refine ⟨hmax d e hde (m e).asIdeal (hm e).1, ?_⟩
      have hnat : (c.ι.app e).hom.comp (F.map (homOfLE hde)).hom =
          (c.ι.app d).hom := congrArg CommRingCat.Hom.hom (c.w (homOfLE hde))
      change p.asIdeal.comap (c.ι.app d).hom ≤
        ((m e).asIdeal.comap (F.map (homOfLE hde)).hom)
      rw [← hnat, ← Ideal.comap_comap]
      exact Ideal.comap_mono (hm e).2
    let M : PrimeSpectrum c.pt := E.symm ⟨m, hcompat⟩
    have hM (d : D) : PrimeSpectrum.comap (c.ι.app d).hom M = m d := by
      rw [← hcoord, E.apply_symm_apply]
    have hpM : p.asIdeal ≤ M.asIdeal := hle fun d ↦ by
      rw [hM]
      exact (hm d).2
    have hMmax : M.asIdeal.IsMaximal := hmax_of_coords M fun d ↦ by
      change (PrimeSpectrum.comap (c.ι.app d).hom M).asIdeal.IsMaximal
      rw [hM]
      exact (hm d).1
    have hqM (q : PrimeSpectrum c.pt) (hpq : p.asIdeal ≤ q.asIdeal) :
        q.asIdeal ≤ M.asIdeal := by
      apply hle
      intro d
      obtain ⟨n, hn, hqn⟩ :=
        (PrimeSpectrum.comap (c.ι.app d).hom q).asIdeal.exists_le_maximal
          (q.isPrime.comap _).ne_top
      have hn_eq : (⟨n, hn.isPrime⟩ : PrimeSpectrum (F.obj d)) = m d :=
        huniq d _ ⟨hn, (Ideal.comap_mono hpq).trans hqn⟩
      rw [hM, ← hn_eq]
      exact hqn
    refine ⟨M.asIdeal, hMmax, hpM, ?_, ?_⟩
    · intro n hn hpn
      exact hn.eq_of_le hMmax.ne_top (hqM ⟨n, hn.isPrime⟩ hpn)
    · intro d
      change (PrimeSpectrum.comap (c.ι.app d).hom M).asIdeal.IsMaximal ∧
        p.asIdeal.comap (c.ι.app d).hom ≤
          (PrimeSpectrum.comap (c.ι.app d).hom M).asIdeal ∧
        ∀ n : Ideal (F.obj d), n.IsMaximal →
          p.asIdeal.comap (c.ι.app d).hom ≤ n →
          n = (PrimeSpectrum.comap (c.ι.app d).hom M).asIdeal
      rw [hM]
      refine ⟨(hm d).1, (hm d).2, ?_⟩
      intro n hn hpn
      exact congrArg PrimeSpectrum.asIdeal (huniq d ⟨n, hn.isPrime⟩ ⟨hn, hpn⟩)
  have hmaximal (p : PrimeSpectrum c.pt) : p.asIdeal.IsMaximal ↔
      ∀ d, (p.asIdeal.comap (c.ι.app d).hom).IsMaximal := by
    refine ⟨?_, hmax_of_coords p⟩
    intro hp
    obtain ⟨m, hm, hpm, _, hmd⟩ := hfirst p
    have hpm_eq := hp.eq_of_le hm.ne_top hpm
    intro d
    rw [hpm_eq]
    exact (hmd d).1
  have hclosed : closedPoints (PrimeSpectrum c.pt) =
      ⋂ d : D, (PrimeSpectrum.comap (c.ι.app d).hom) ⁻¹'
        closedPoints (PrimeSpectrum (F.obj d)) := by
    ext p
    simp only [Set.mem_iInter, Set.mem_preimage, mem_closedPoints_iff,
      isClosed_singleton_iff_isMaximal]
    exact hmaximal p
  have hW : IsWLocalRing c.pt := by
    refine ⟨{ eq_of_specializes := ?_, isClosed_closedPoints := ?_ }⟩
    · intro p m n hm hn hpm hpn
      obtain ⟨a, ha, hpa, huniq, _⟩ := hfirst p
      apply PrimeSpectrum.ext
      exact (huniq m.asIdeal ((isClosed_singleton_iff_isMaximal m).mp hm)
        ((le_iff_specializes p m).mpr hpm)).trans
        (huniq n.asIdeal ((isClosed_singleton_iff_isMaximal n).mp hn)
          ((le_iff_specializes p n).mpr hpn)).symm
    · rw [hclosed]
      exact isClosed_iInter fun d ↦
        WLocalSpace.isClosed_closedPoints.preimage (continuous_comap _)
  have : IsWLocalRing c.pt := hW
  have hcp (m : closedPoints (PrimeSpectrum c.pt)) (d : D) :
      PrimeSpectrum.comap (c.ι.app d).hom m.val ∈
        closedPoints (PrimeSpectrum (F.obj d)) :=
    (isClosed_singleton_iff_isMaximal _).mpr
      ((hmaximal m.val).mp ((isClosed_singleton_iff_isMaximal _).mp m.property) d)
  let CP := {p : (d : D) → closedPoints (PrimeSpectrum (F.obj d)) //
    ∀ (d e : D) (hde : d ≤ e),
      PrimeSpectrum.comap (F.map (homOfLE hde)).hom (p e).val = (p d).val}
  let f : closedPoints (PrimeSpectrum c.pt) → CP := fun m ↦
    ⟨fun d ↦ ⟨PrimeSpectrum.comap (c.ι.app d).hom m.val, hcp m d⟩, by
      intro d e hde
      rw [← comap_comp_apply]
      exact congrArg (fun t : F.obj d ⟶ c.pt ↦ PrimeSpectrum.comap t.hom m.val)
        (c.w (homOfLE hde))⟩
  have hfcont : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro d
    exact ((continuous_comap _).comp continuous_subtype_val).subtype_mk _
  have hfbij : Function.Bijective f := by
    constructor
    · intro m n hmn
      apply Subtype.ext
      exact hinj fun d ↦ congrArg (fun p : CP ↦ (p.val d).val) hmn
    · intro p
      let q : PrimeSpectrum c.pt := E.symm
        ⟨fun d ↦ (p.val d).val, p.property⟩
      have hq (d : D) : PrimeSpectrum.comap (c.ι.app d).hom q = (p.val d).val := by
        rw [← hcoord, E.apply_symm_apply]
      have hqcp : q ∈ closedPoints (PrimeSpectrum c.pt) := by
        apply (isClosed_singleton_iff_isMaximal _).mpr
        apply hmax_of_coords
        intro d
        change (PrimeSpectrum.comap (c.ι.app d).hom q).asIdeal.IsMaximal
        rw [hq]
        exact (isClosed_singleton_iff_isMaximal _).mp (p.val d).property
      refine ⟨⟨q, hqcp⟩, ?_⟩
      apply Subtype.ext
      funext d
      apply Subtype.ext
      exact hq d
  let ec : closedPoints (PrimeSpectrum c.pt) ≃ₜ CP :=
    (isHomeomorph_iff_continuous_bijective.mpr ⟨hfcont, hfbij⟩).homeomorph
  let H : closedPoints (PrimeSpectrum c.pt) ≃ₜ
      ConnectedComponents (PrimeSpectrum c.pt) := WLocalSpace.closedPointsHomeomorph
  let Hd (d : D) : closedPoints (PrimeSpectrum (F.obj d)) ≃ₜ
      ConnectedComponents (PrimeSpectrum (F.obj d)) := WLocalSpace.closedPointsHomeomorph
  let CC := {p : (d : D) → ConnectedComponents (PrimeSpectrum (F.obj d)) //
    ∀ (d e : D) (hde : d ≤ e),
      (continuous_comap (F.map (homOfLE hde)).hom).connectedComponentsMap (p e) = p d}
  let g : ConnectedComponents (PrimeSpectrum c.pt) → CC := fun z ↦
    ⟨fun d ↦ (continuous_comap (c.ι.app d).hom).connectedComponentsMap z, by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
      intro d e hde
      simp only [Continuous.connectedComponentsMap_mk]
      rw [← comap_comp_apply]
      exact congrArg (fun t : F.obj d ⟶ c.pt ↦
        ConnectedComponents.mk (PrimeSpectrum.comap t.hom x)) (c.w (homOfLE hde))⟩
  have hgcont : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_pi fun d ↦
      (continuous_comap (c.ι.app d).hom).connectedComponentsMap_continuous
  have hgbij : Function.Bijective g := by
    constructor
    · intro z w hzw
      obtain ⟨m, rfl⟩ := H.surjective z
      obtain ⟨n, rfl⟩ := H.surjective w
      apply congrArg H
      apply Subtype.ext
      apply hinj
      intro d
      exact WLocalSpace.closedPoints_eq_of_mk_eq (hcp m d) (hcp n d)
        (congrArg (fun p : CC ↦ p.val d) hzw)
    · intro p
      let a (d : D) := (Hd d).symm (p.val d)
      have ha (d e : D) (hde : d ≤ e) :
          PrimeSpectrum.comap (F.map (homOfLE hde)).hom (a e).val = (a d).val := by
        apply WLocalSpace.closedPoints_eq_of_mk_eq
          ((isClosed_singleton_iff_isMaximal _).mpr
            (hmax d e hde (a e).val.asIdeal
              ((isClosed_singleton_iff_isMaximal _).mp (a e).property))) (a d).property
        have hae : ConnectedComponents.mk (a e).val = p.val e :=
          (Hd e).apply_symm_apply _
        have had : ConnectedComponents.mk (a d).val = p.val d :=
          (Hd d).apply_symm_apply _
        rw [← Continuous.connectedComponentsMap_mk, hae, had]
        exact p.property d e hde
      obtain ⟨m, hm⟩ := ec.surjective ⟨a, ha⟩
      refine ⟨H m, ?_⟩
      apply Subtype.ext
      funext d
      have hmd : PrimeSpectrum.comap (c.ι.app d).hom m.val = (a d).val :=
        congrArg (fun p : CP ↦ (p.val d).val) hm
      change ConnectedComponents.mk (PrimeSpectrum.comap (c.ι.app d).hom m.val) = _
      rw [hmd]
      exact (Hd d).apply_symm_apply _
  let eg : ConnectedComponents (PrimeSpectrum c.pt) ≃ₜ CC :=
    (isHomeomorph_iff_continuous_bijective.mpr ⟨hgcont, hgbij⟩).homeomorph
  exact ⟨hfirst, hmaximal, hclosed, hW,
    ⟨ec, fun _ _ ↦ rfl⟩,
    ⟨eg, fun x d ↦
      Continuous.connectedComponentsMap_mk (continuous_comap (c.ι.app d).hom) x⟩⟩

end PrimeSpectrum

end
