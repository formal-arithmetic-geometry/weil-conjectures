/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.IndZariskiOfWLocal
public import WeilConjectures.Topology.SpectralSpace.WLocal.Partition

/-!
# Points of w-local algebras identifying local rings

Let `A → B` identify local rings, with `Spec B` w-local. Every point `P` of `Spec B` specializes
to a unique closed point `c(P)`, and we record `P` by the pair `(x, y) = (c(P) ∩ A, P ∩ A)` of
primes of `A` with `y ⊆ x`. If `Spec B → Spec A` is injective on closed points, this identifies
`Spec B` with the pairs `(x, y)` with `x` in the image of the closed points and `y ⊆ x`; the local
ring at `(x, y)` is `A_y`, and the connected component of the closed point over `x` is
`Spec A_x`.

We apply this to the w-localization `A^w` (blueprint `lem-weil-pbc-w-localization-points`).
-/

@[expose] public section

open PrimeSpectrum Topology

namespace WLocalSpace

variable {X : Type*} [TopologicalSpace X] [WLocalSpace X]

/-- The unique closed point to which a point of a w-local space specializes. -/
noncomputable def closedPoint (x : X) : X :=
  (exists_isClosed_specializes x).choose

lemma isClosed_closedPoint (x : X) : IsClosed {closedPoint x} :=
  (exists_isClosed_specializes x).choose_spec.1

lemma specializes_closedPoint (x : X) : x ⤳ closedPoint x :=
  (exists_isClosed_specializes x).choose_spec.2

lemma closedPoint_eq {x c : X} (hc : IsClosed {c}) (hxc : x ⤳ c) : closedPoint x = c :=
  eq_of_specializes (isClosed_closedPoint x) hc (specializes_closedPoint x) hxc

/-- The connected component of a closed point `c` of a w-local space consists of the points
specializing to `c`. -/
lemma connectedComponent_eq_setOf_specializes {c : X} (hc : IsClosed {c}) :
    connectedComponent c = {x | x ⤳ c} := by
  have hcomp : ∀ {x y : X}, x ⤳ y → connectedComponent x = connectedComponent y :=
    fun {x y} hxy ↦ (connectedComponent_eq_iff_mem.mpr
      ((isConnected_singleton (x := x)).closure.subset_connectedComponent
        (subset_closure rfl) (specializes_iff_mem_closure.mp hxy))).symm
  ext x
  change x ∈ connectedComponent c ↔ x ⤳ c
  constructor
  · intro hx
    have h1 : connectedComponent x = connectedComponent c := connectedComponent_eq_iff_mem.mpr hx
    have h2 := hcomp (specializes_closedPoint x)
    have : closedPoint x = c := closedPoints_eq_of_mk_eq
      (mem_closedPoints_iff.mpr (isClosed_closedPoint x)) (mem_closedPoints_iff.mpr hc)
      (ConnectedComponents.coe_eq_coe.mpr (h2.symm.trans h1))
    exact this ▸ specializes_closedPoint x
  · intro hxc
    exact connectedComponent_eq_iff_mem.mp (hcomp hxc)

end WLocalSpace

namespace IsWLocalRing

open WLocalSpace

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsWLocalRing B]

variable (A) in
/-- A point `P` of `Spec B` recorded as the pair `(c(P) ∩ A, P ∩ A)`. -/
noncomputable def pointPair (P : PrimeSpectrum B) : PrimeSpectrum A × PrimeSpectrum A :=
  (comap (algebraMap A B) (closedPoint P), comap (algebraMap A B) P)

omit [IsWLocalRing B] in
lemma comap_le_comap {P Q : PrimeSpectrum B} (h : P ≤ Q) :
    comap (algebraMap A B) P ≤ comap (algebraMap A B) Q :=
  Ideal.comap_mono (f := algebraMap A B) h

lemma pointPair_snd_le (P : PrimeSpectrum B) : (pointPair A P).2 ≤ (pointPair A P).1 :=
  comap_le_comap ((le_iff_specializes P _).mpr (specializes_closedPoint P))

omit [IsWLocalRing B] in
lemma mem_range_comap_atPrime_iff (c P : PrimeSpectrum B) :
    P ∈ Set.range (comap (algebraMap B (Localization.AtPrime c.asIdeal))) ↔ P ≤ c := by
  rw [localization_comap_range (Localization.AtPrime c.asIdeal) c.asIdeal.primeCompl]
  change Disjoint (c.asIdeal.primeCompl : Set B) P.asIdeal ↔ P.asIdeal ≤ c.asIdeal
  rw [Set.disjoint_left]
  constructor
  · intro h a ha
    by_contra hac
    exact h (Ideal.mem_primeCompl_iff.mpr hac) ha
  · intro h a hac haP
    exact (Ideal.mem_primeCompl_iff.mp hac) (h haP)

variable [Algebra.BijectiveOnStalks A B]

/-- The stalk isomorphism `A_x → B_c` at a point `c` of `Spec B` over `x`. -/
noncomputable def stalkHom (c : PrimeSpectrum B) :
    Localization.AtPrime (comap (algebraMap A B) c).asIdeal →+* Localization.AtPrime c.asIdeal :=
  Localization.localRingHom (c.asIdeal.comap (algebraMap A B)) c.asIdeal (algebraMap A B) rfl

omit [IsWLocalRing B] in
lemma bijective_stalkHom (c : PrimeSpectrum B) : Function.Bijective (stalkHom (A := A) c) :=
  Algebra.BijectiveOnStalks.bijective_localRingHom c.asIdeal

omit [IsWLocalRing B] [Algebra.BijectiveOnStalks A B] in
lemma comap_stalkHom_comap (c : PrimeSpectrum B)
    (Q : PrimeSpectrum (Localization.AtPrime c.asIdeal)) :
    comap (algebraMap A (Localization.AtPrime (comap (algebraMap A B) c).asIdeal))
        (comap (stalkHom c) Q) =
      comap (algebraMap A B) (comap (algebraMap B (Localization.AtPrime c.asIdeal)) Q) := by
  rw [← comap_comp_apply, ← comap_comp_apply]
  congr 2
  ext a
  simp [stalkHom, Localization.localRingHom_to_map]

omit [IsWLocalRing B] in
/-- Two points below the same point `c` with the same image in `Spec A` are equal. -/
lemma eq_of_le_of_comap_eq {c P P' : PrimeSpectrum B} (hP : P ≤ c) (hP' : P' ≤ c)
    (h : comap (algebraMap A B) P = comap (algebraMap A B) P') : P = P' := by
  obtain ⟨Q, rfl⟩ := (mem_range_comap_atPrime_iff c P).mpr hP
  obtain ⟨Q', rfl⟩ := (mem_range_comap_atPrime_iff c P').mpr hP'
  rw [← comap_stalkHom_comap, ← comap_stalkHom_comap] at h
  have h1 := localization_comap_injective _
    (comap (algebraMap A B) c).asIdeal.primeCompl h
  rw [comap_injective_of_surjective _ (bijective_stalkHom (A := A) c).2 h1]

omit [IsWLocalRing B] in
/-- Every prime `y ⊆ x` of `A`, where `x` lies under `c`, is the image of a point of `Spec B`
below `c`. -/
lemma exists_le_comap_eq {c : PrimeSpectrum B} {y : PrimeSpectrum A}
    (hy : y ≤ comap (algebraMap A B) c) :
    ∃ P : PrimeSpectrum B, P ≤ c ∧ comap (algebraMap A B) P = y := by
  set x := comap (algebraMap A B) c
  have hy' : y ∈ Set.range (comap (algebraMap A (Localization.AtPrime x.asIdeal))) := by
    rw [localization_comap_range (Localization.AtPrime x.asIdeal) x.asIdeal.primeCompl]
    change Disjoint (x.asIdeal.primeCompl : Set A) y.asIdeal
    rw [Set.disjoint_left]
    intro a hax hay
    exact (Ideal.mem_primeCompl_iff.mp hax) (hy hay)
  obtain ⟨yt, rfl⟩ := hy'
  let e := RingEquiv.ofBijective _ (bijective_stalkHom (A := A) c)
  set Q := comap e.symm.toRingHom yt
  have hQ : comap (stalkHom c) Q = yt := by
    rw [← comap_comp_apply]
    have : e.symm.toRingHom.comp (stalkHom c) = RingHom.id _ := by
      ext z
      exact e.symm_apply_apply z
    rw [this, comap_id]
  refine ⟨comap (algebraMap B (Localization.AtPrime c.asIdeal)) Q,
    (mem_range_comap_atPrime_iff c _).mp ⟨Q, rfl⟩, ?_⟩
  rw [← comap_stalkHom_comap, hQ]

/-- If `Spec B → Spec A` is injective on closed points, a point of `Spec B` is determined by its
pair `(c(P) ∩ A, P ∩ A)`. -/
theorem pointPair_injective
    (hinj : Set.InjOn (comap (algebraMap A B)) (closedPoints (PrimeSpectrum B))) :
    Function.Injective (pointPair A (B := B)) := by
  intro P P' h
  simp only [pointPair, Prod.mk.injEq] at h
  have hc : closedPoint P = closedPoint P' :=
    hinj (mem_closedPoints_iff.mpr (isClosed_closedPoint P))
      (mem_closedPoints_iff.mpr (isClosed_closedPoint P')) h.1
  refine eq_of_le_of_comap_eq (c := closedPoint P)
    ((le_iff_specializes P _).mpr (specializes_closedPoint P)) ?_ h.2
  rw [hc]
  exact (le_iff_specializes P' _).mpr (specializes_closedPoint P')

/-- The pairs `(c(P) ∩ A, P ∩ A)` are exactly the pairs `(x, y)` with `y ⊆ x` and `x` the image
of a closed point. -/
theorem range_pointPair :
    Set.range (pointPair A (B := B)) =
      {z | z.1 ∈ comap (algebraMap A B) '' closedPoints (PrimeSpectrum B) ∧ z.2 ≤ z.1} := by
  ext ⟨x, y⟩
  simp only [Set.mem_range, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨P, hP⟩
    simp only [pointPair, Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl⟩ := hP
    exact ⟨⟨closedPoint P, mem_closedPoints_iff.mpr (isClosed_closedPoint P), rfl⟩,
      pointPair_snd_le P⟩
  · rintro ⟨⟨c, hc, rfl⟩, hyx⟩
    obtain ⟨P, hPc, rfl⟩ := exists_le_comap_eq hyx
    refine ⟨P, ?_⟩
    simp only [pointPair, Prod.mk.injEq, and_true]
    rw [closedPoint_eq (mem_closedPoints_iff.mp hc) ((le_iff_specializes P c).mp hPc)]

/-- The connected component of a closed point `c` of `Spec B` is the image of `Spec B_c`, and
`B_c` is isomorphic to `A_x` for `x = c ∩ A`. -/
theorem connectedComponent_eq_range {c : PrimeSpectrum B} (hc : IsClosed {c}) :
    connectedComponent c = Set.range (comap (algebraMap B (Localization.AtPrime c.asIdeal))) ∧
      Nonempty (Localization.AtPrime (comap (algebraMap A B) c).asIdeal ≃+*
        Localization.AtPrime c.asIdeal) := by
  refine ⟨?_, ⟨RingEquiv.ofBijective _ (bijective_stalkHom (A := A) c)⟩⟩
  rw [connectedComponent_eq_setOf_specializes hc]
  ext P
  rw [mem_range_comap_atPrime_iff, le_iff_specializes]
  rfl

/-- If `Spec B → Spec A` maps the closed points of `Spec B` bijectively onto `Spec A`, the
closed points of `Spec B` are homeomorphic to `Spec A` with its patch topology. -/
theorem isHomeomorph_closedPoints_constructible
    (hbij : Set.BijOn (comap (algebraMap A B)) (closedPoints (PrimeSpectrum B)) Set.univ) :
    IsHomeomorph (fun c : closedPoints (PrimeSpectrum B) ↦
      (WithTopology.toTopology (constructibleTopology (PrimeSpectrum A))
        (comap (algebraMap A B) c) : WithConstructibleTopology (PrimeSpectrum A))) := by
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨?_, ⟨fun c c' h ↦ Subtype.ext (hbij.injOn c.2 c'.2
    (congrArg WithTopology.ofTopology h)), fun z ↦ ?_⟩⟩
  · have hg : Continuous[_, constructibleTopology (PrimeSpectrum A)]
        (fun c : closedPoints (PrimeSpectrum B) ↦ comap (algebraMap A B) c.1) := by
      rw [continuous_generateFrom_iff]
      rintro s (⟨hso, -⟩ | ⟨hscl, hsc⟩)
      · exact hso.preimage ((PrimeSpectrum.continuous_comap (algebraMap A B)).comp continuous_subtype_val)
      · obtain ⟨t, ht⟩ := isCompact_isOpen_iff.mp ⟨hsc, hscl.isOpen_compl⟩
        have hs : s = zeroLocus (t : Set A) := by rw [← compl_compl s, ← ht, compl_compl]
        subst hs
        rw [← isClosed_compl_iff]
        have : ((fun c : closedPoints (PrimeSpectrum B) ↦ comap (algebraMap A B) c.1) ⁻¹'
            zeroLocus (t : Set A))ᶜ = ⋃ f ∈ t,
              Subtype.val ⁻¹' (basicOpen (algebraMap A B f) : Set (PrimeSpectrum B)) := by
          ext c
          simp [Set.subset_def]
        rw [this]
        refine isClosed_biUnion_finset fun f _ ↦ ?_
        have := (IsWLocalRing.isClosed_closedPoints_inter_basicOpen
          (algebraMap A B f)).preimage
          (continuous_subtype_val (p := (· ∈ closedPoints (PrimeSpectrum B))))
        rwa [Set.preimage_inter, Subtype.coe_preimage_self, Set.univ_inter] at this
    exact @Continuous.comp _ _ _ _ (constructibleTopology _) _ _ _ continuous_coinduced_rng hg
  · obtain ⟨c, hc, hcz⟩ := hbij.surjOn (Set.mem_univ z.ofTopology)
    exact ⟨⟨c, hc⟩, by simp [hcz]⟩

end IsWLocalRing

open IsWLocalRing

/-- **Blueprint `lem-weil-pbc-w-localization-points`**: the points of `Spec A^w` are the pairs
`(x, y)` of primes of `A` with `y ⊆ x` (via `P ↦ (c(P) ∩ A, P ∩ A)`), with local ring `A_y`;
the connected component of the closed point over `x` is `Spec (A^w)_c ≅ Spec A_x`; the closed
points are homeomorphic to `Spec A` with its patch topology; `A → A^w` is faithfully flat and
`Spec A^w` is w-local. -/
theorem WLocalization.points_spec (A : Type*) [CommRing A] :
    Function.Injective (pointPair A (B := WLocalization A)) ∧
      Set.range (pointPair A (B := WLocalization A)) = {z | z.2 ≤ z.1} ∧
      (∀ P : PrimeSpectrum (WLocalization A), Function.Bijective
        (Localization.localRingHom (P.asIdeal.comap (algebraMap A (WLocalization A))) P.asIdeal
          (algebraMap A (WLocalization A)) rfl)) ∧
      (∀ c : PrimeSpectrum (WLocalization A), IsClosed {c} →
        connectedComponent c =
          Set.range (comap (algebraMap (WLocalization A) (Localization.AtPrime c.asIdeal))) ∧
        Nonempty (Localization.AtPrime (comap (algebraMap A (WLocalization A)) c).asIdeal ≃+*
          Localization.AtPrime c.asIdeal)) ∧
      IsHomeomorph (fun c : closedPoints (PrimeSpectrum (WLocalization A)) ↦
        (WithTopology.toTopology (constructibleTopology (PrimeSpectrum A))
          (comap (algebraMap A (WLocalization A)) c) :
            WithConstructibleTopology (PrimeSpectrum A))) ∧
      Module.FaithfullyFlat A (WLocalization A) ∧ IsWLocalRing (WLocalization A) := by
  have hbij : Set.BijOn (comap (algebraMap A (WLocalization A)))
      (closedPoints (PrimeSpectrum (WLocalization A))) Set.univ :=
    WLocalization.zeroLocus_ideal_eq A ▸ WLocalization.bijOn_algebraMap_specComap_zeroLocus_ideal A
  refine ⟨pointPair_injective hbij.injOn, ?_, fun P ↦
    Algebra.BijectiveOnStalks.bijective_localRingHom P.asIdeal,
    fun c hc ↦ connectedComponent_eq_range hc, isHomeomorph_closedPoints_constructible hbij,
    inferInstance, inferInstance⟩
  rw [range_pointPair, hbij.image_eq]
  simp

/-- **Blueprint `lem-weil-pbc-retained-localization`** (for `T = V(I)` consisting of closed
points): `A → A_{[T]}` is ind-Zariski; the points of `Spec A_{[T]}` are the pairs `(x, y)` with
`x ∈ T` and `y ⊆ x`, with local ring `A_y`; `Spec A_{[T]}` is w-local with closed points lying
bijectively over `T`; and `A ⧸ I → A_{[T]} ⧸ I A_{[T]}` is an isomorphism. -/
theorem Ideal.WLocalization.retained_spec {A : Type*} [CommRing A] (I : Ideal A)
    (hI : PrimeSpectrum.zeroLocus (I : Set A) ⊆ closedPoints (PrimeSpectrum A)) :
    Algebra.IndZariski A I.WLocalization ∧
      Function.Injective (pointPair A (B := I.WLocalization)) ∧
      Set.range (pointPair A (B := I.WLocalization)) = {z | z.1 ∈ PrimeSpectrum.zeroLocus (I : Set A) ∧ z.2 ≤ z.1} ∧
      (∀ P : PrimeSpectrum I.WLocalization, Function.Bijective
        (Localization.localRingHom (P.asIdeal.comap (algebraMap A I.WLocalization)) P.asIdeal
          (algebraMap A I.WLocalization) rfl)) ∧
      IsWLocalRing I.WLocalization ∧
      Set.BijOn (PrimeSpectrum.comap (algebraMap A I.WLocalization))
        (closedPoints (PrimeSpectrum I.WLocalization)) (PrimeSpectrum.zeroLocus (I : Set A)) ∧
      Function.Bijective (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map) := by
  have hbij : Set.BijOn (PrimeSpectrum.comap (algebraMap A I.WLocalization))
      (closedPoints (PrimeSpectrum I.WLocalization)) (PrimeSpectrum.zeroLocus (I : Set A)) :=
    zeroLocus_map_algebraMap_eq_closedPoints hI ▸
      bijOn_zeroLocus_map I hI
  refine ⟨inferInstance, pointPair_injective hbij.injOn, ?_, fun P ↦
    Algebra.BijectiveOnStalks.bijective_localRingHom P.asIdeal, inferInstance, hbij,
    quotientMap_algebraMap_bijective I hI⟩
  rw [range_pointPair, hbij.image_eq]
