/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.CategoryTheory.FilteredComplexQuotientCoherence
public import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology
import Sheaf.CategoryTheory.FilteredComplexQuotientMap
import all WeilConjectures.CategoryTheory.FilteredQuotientPageMaps
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCover
import Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis

/-! # The coherent quotient spectral sequence of a filtered complex

Source: Stacks Project, Tag 012K, cycle and boundary construction and functoriality.
(blueprint: lem-sp-filtered-complex-canonical-sequence).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The unique differential specified on cycle representatives.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence). -/
noncomputable def filteredComplexCanonicalDifferential
    (U : FilteredObject (CochainComplex C ℤ)) (r : ℤ) (hr : 1 ≤ r) :
    FilteredComplexPageDifferential U.obj U.filtration r :=
  (filteredComplex_page_differential_exists_unique U.obj U.filtration r hr).choose

/-- The uniquely normalized successor comparison.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence). -/
noncomputable def filteredComplexCanonicalHomology
    (U : FilteredObject (CochainComplex C ℤ)) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
    (filteredComplexCanonicalDifferential U r hr).page.homology pq ≅
      filteredComplexPageObject U.obj U.filtration (r + 1) pq :=
  (filteredComplex_normalized_homology U.obj U.filtration r hr
    (filteredComplexCanonicalDifferential U r hr) pq).choose

/-- Assemble the concrete pages and the uniquely normalized homology comparisons.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence). -/
noncomputable def filteredComplexCanonicalSequence
    (U : FilteredObject (CochainComplex C ℤ)) : CohomologicalSpectralSequence C 1 where
  page r hr := (filteredComplexCanonicalDifferential U r hr).page
  iso r _r' pq hrr' hr := filteredComplexCanonicalHomology U r hr pq ≪≫
    eqToIso (congrArg (fun s ↦ filteredComplexPageObject U.obj U.filtration s pq) hrr')

/-- The pages are the constructed boundary quotients.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence). -/
noncomputable def filteredComplexCanonicalPageIso
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 1 ≤ r) :
    ((filteredComplexCanonicalSequence U).page r hr).X (p, q) ≅
      filteredComplexPageObject U.obj U.filtration r (p, q) := Iso.refl _

/-- The successor comparisons act on representatives by the actual quotient projection.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence).

Proof. The chosen differential is specified uniquely on representatives. The chosen
homology isomorphism is the uniquely normalized one. Cover the cycles by successor
cycles; the monic cycle inclusion identifies an arbitrary test representative with
its composite through this cover. Its normalization equation gives the successor law. -/
theorem filteredComplexCanonicalSequence_coherence
    (U : FilteredObject (CochainComplex C ℤ)) :
    FilteredComplexQuotientCoherence U.obj U.filtration
      (filteredComplexCanonicalSequence U) (filteredComplexCanonicalPageIso U) := by
  constructor
  · intro r hr
    exact ⟨filteredComplexCanonicalDifferential U r hr, Iso.refl _, fun _ _ ↦ rfl⟩
  · intro r hr p q hZ A x z hz
    let D := filteredComplexCanonicalDifferential U r hr
    obtain ⟨f, _, hf⟩ :=
      filteredComplex_successor_cycles_cover U.obj U.filtration r hr D (p, q) hZ
    change z ≫ D.page.iCycles (p, q) =
      x ≫ Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ U.obj U.filtration r (p, q) ≫
        (Iso.refl _).inv at hz
    simp only [Iso.refl_inv, Category.comp_id] at hz
    have hzf : z = x ≫ f := by
      apply (cancel_mono (D.page.iCycles (p, q))).1
      simpa only [Category.assoc, hf] using hz
    have hn := (filteredComplex_normalized_homology U.obj U.filtration r hr D
      (p, q)).choose_spec.1 hZ f hf
    simp only [filteredComplexCanonicalSequence, Iso.trans_hom, eqToIso_refl,
      Iso.refl_hom, filteredComplexCanonicalPageIso, Category.comp_id]
    change z ≫ D.page.homologyπ (p, q) ≫
        (filteredComplexCanonicalHomology U r hr (p, q)).hom = _
    simp only [hzf, Category.assoc]
    exact congrArg (fun a ↦ x ≫ a) hn

/-- Canonical page maps are specified by the restriction, graded, cycle and quotient squares.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence). -/
def FilteredComplexCanonicalMapProperty
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V)
    (N : filteredComplexCanonicalSequence U ⟶ filteredComplexCanonicalSequence V) : Prop :=
  ∀ (p q r : ℤ) (hr : 1 ≤ r)
    (s : ∀ a : ℤ, (U.filtration.step a : CochainComplex C ℤ) ⟶
      (V.filtration.step a : CochainComplex C ℤ))
    (g : U.filtration.gradedPiece p ⟶ V.filtration.gradedPiece p)
    (kz : (U.filtration.complexCycles p (p + q) r : C) ⟶
      (V.filtration.complexCycles p (p + q) r : C))
    (k : filteredComplexPageObject U.obj U.filtration r (p, q) ⟶
      filteredComplexPageObject V.obj V.filtration r (p, q)),
    (∀ a, s a ≫ (V.filtration.step a).arrow = (U.filtration.step a).arrow ≫ t.hom) →
    U.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
      s p ≫ V.filtration.complexQuotientπ p (p + 1) (by omega) →
    kz ≫ (V.filtration.complexCycles p (p + q) r).arrow =
      (U.filtration.complexCycles p (p + q) r).arrow ≫ g.f (p + q) →
    filteredComplexPageπ U.obj U.filtration r (p, q) ≫ k =
      kz ≫ filteredComplexPageπ V.obj V.filtration r (p, q) →
    (N.hom r hr).f (p, q) = k

/-- Existence and uniqueness of the spectral-sequence map specified by the four squares.
Source: Stacks, Tag 012K, Lemma 12.24.4
(blueprint: lem-sp-filtered-complex-canonical-sequence).

Proof. Apply coherent quotient descent to the normalized sequences. On the epic
cover of graded cycles by unquotiented representatives its equation identifies the
induced page map with every map satisfying the four squares. The cycle cover and
quotient projection are epic. Conversely the concrete cokernel page maps supply
these squares in every bidegree, so this property determines every page component. -/
theorem filteredComplexCanonicalMap_exists_unique
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) :
    ∃! N : filteredComplexCanonicalSequence U ⟶ filteredComplexCanonicalSequence V,
      FilteredComplexCanonicalMapProperty t N := by
  obtain ⟨N, hN⟩ := filteredComplex_quotient_map U.obj V.obj U.filtration V.filtration
    (filteredComplexCanonicalSequence U) (filteredComplexCanonicalSequence V)
    (filteredComplexCanonicalPageIso U) (filteredComplexCanonicalPageIso V)
    (filteredComplexCanonicalSequence_coherence U) (filteredComplexCanonicalSequence_coherence V)
    t.hom t.preserves
  have hprop : FilteredComplexCanonicalMapProperty t N := by
    intro p q r hr s g kz k hs hg hkz hk
    obtain ⟨z, _, hepi, _, hz, _⟩ :=
      U.filtration.filteredComplex_representative_epis p (p + q) r (by omega)
    have : Epi z := hepi
    have : Epi (filteredComplexPageπ U.obj U.filtration r (p, q)) := by
      unfold filteredComplexPageπ
      infer_instance
    apply (cancel_epi (z ≫ filteredComplexPageπ U.obj U.filtration r (p, q))).1
    have hsi := congrArg (fun a ↦ a.f (p + q)) (hs p)
    have hgi := congrArg (fun a ↦ a.f (p + q)) hg
    simp only [HomologicalComplex.comp_f] at hsi hgi
    have hrep := hN _ p q r hr
      (U.filtration.complexCycleRepresentatives p (p + q) r).arrow
      ((U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫ (s p).f (p + q))
      z (z ≫ kz) (by rw [Category.assoc, hsi]) hz (by
        rw [Category.assoc, hkz, ← Category.assoc, hz, Category.assoc, hgi]
        simp only [Category.assoc])
    dsimp only [filteredComplexCanonicalPageIso, Iso.refl_inv,
      filteredComplexCanonicalSequence, FilteredComplexPageDifferential.page] at hrep
    simpa only [Category.comp_id, Category.id_comp, Category.assoc, hk] using hrep
  refine ⟨N, hprop, ?_⟩
  intro N' hN'
  apply SpectralSequence.hom_ext
  intro r hr
  apply HomologicalComplex.Hom.ext
  funext pq
  rcases pq with ⟨p, q⟩
  let S := quotientPageSquares t r
  exact (hN' p q r hr S.s (S.g p) (S.kz (p, q)) (S.k (p, q))
    S.hs (S.hg p) (S.hkz (p, q)) (S.hk (p, q))).trans
      (hprop p q r hr S.s (S.g p) (S.kz (p, q)) (S.k (p, q))
        S.hs (S.hg p) (S.hkz (p, q)) (S.hk (p, q))).symm

/-- The unique map induced by a filtered chain map.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence). -/
noncomputable def filteredComplexCanonicalMap
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) :
    filteredComplexCanonicalSequence U ⟶ filteredComplexCanonicalSequence V :=
  (filteredComplexCanonicalMap_exists_unique t).choose

/-- The constructed map has its defining four-square property.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence). -/
theorem filteredComplexCanonicalMap_property
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) :
    FilteredComplexCanonicalMapProperty t (filteredComplexCanonicalMap t) :=
  (filteredComplexCanonicalMap_exists_unique t).choose_spec.1

/-- Identity maps act by identity on the canonical sequence.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence). -/
theorem filteredComplexCanonicalMap_id (U : FilteredObject (CochainComplex C ℤ)) :
    filteredComplexCanonicalMap (𝟙 U) = 𝟙 _ := by
  apply SpectralSequence.hom_ext
  intro r hr
  apply HomologicalComplex.Hom.ext
  funext pq
  rcases pq with ⟨p, q⟩
  exact filteredComplexCanonicalMap_property (𝟙 U) p q r hr
    (fun _ ↦ 𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    (by intro a; change 𝟙 _ ≫ _ = _ ≫ 𝟙 _; simp)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Composite maps act by the composite of canonical sequence maps.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence). -/
theorem filteredComplexCanonicalMap_comp
    {U V W : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (t' : V ⟶ W) :
    filteredComplexCanonicalMap (t ≫ t') =
      filteredComplexCanonicalMap t ≫ filteredComplexCanonicalMap t' := by
  apply SpectralSequence.hom_ext
  intro r hr
  apply HomologicalComplex.Hom.ext
  funext pq
  rcases pq with ⟨p, q⟩
  let S := quotientPageSquares t r
  let T := quotientPageSquares t' r
  have hS := filteredComplexCanonicalMap_property t p q r hr
    S.s (S.g p) (S.kz (p, q)) (S.k (p, q)) S.hs (S.hg p) (S.hkz (p, q)) (S.hk (p, q))
  have hT := filteredComplexCanonicalMap_property t' p q r hr
    T.s (T.g p) (T.kz (p, q)) (T.k (p, q)) T.hs (T.hg p) (T.hkz (p, q)) (T.hk (p, q))
  change _ = ((filteredComplexCanonicalMap t).hom r hr).f (p, q) ≫
    ((filteredComplexCanonicalMap t').hom r hr).f (p, q)
  rw [hS, hT]
  apply filteredComplexCanonicalMap_property (t ≫ t') p q r hr
    (fun a ↦ S.s a ≫ T.s a) (S.g p ≫ T.g p) (S.kz (p, q) ≫ T.kz (p, q))
    (S.k (p, q) ≫ T.k (p, q))
  · intro a
    change (S.s a ≫ T.s a) ≫ _ = _ ≫ (t.hom ≫ t'.hom)
    rw [Category.assoc, T.hs, ← Category.assoc, S.hs, Category.assoc]
  · rw [← Category.assoc, S.hg, Category.assoc, T.hg, ← Category.assoc]
  · rw [Category.assoc, T.hkz, ← Category.assoc, S.hkz]
    simp only [HomologicalComplex.comp_f, Category.assoc]
  · rw [← Category.assoc, S.hk, Category.assoc, T.hk]
    simp only [Category.assoc]

/-- The coherent filtered-complex spectral sequence is functorial.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence). -/
noncomputable def filteredComplexCanonicalFunctor :
    FilteredObject (CochainComplex C ℤ) ⥤ CohomologicalSpectralSequence C 1 where
  obj := filteredComplexCanonicalSequence
  map := filteredComplexCanonicalMap
  map_id := filteredComplexCanonicalMap_id
  map_comp := filteredComplexCanonicalMap_comp

/-- Discard page one, retaining exactly the chosen pages and successor isomorphisms.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-sequence). -/
noncomputable def filteredComplexCanonicalPageTwoFunctor :
    FilteredObject (CochainComplex C ℤ) ⥤ E₂CohomologicalSpectralSequence C where
  obj U :=
    { page r hr := (filteredComplexCanonicalSequence U).page r (by omega)
      iso r r' pq hrr' hr := (filteredComplexCanonicalSequence U).iso r r' pq hrr' (by omega) }
  map t :=
    { hom r hr := (filteredComplexCanonicalMap t).hom r (by omega)
      comm r r' pq hrr' hr := (filteredComplexCanonicalMap t).comm r r' pq hrr' (by omega) }
  map_id U := by
    apply SpectralSequence.hom_ext
    intro r hr
    change (filteredComplexCanonicalMap (𝟙 U)).hom r _ = _
    rw [filteredComplexCanonicalMap_id]
    rfl
  map_comp t t' := by
    apply SpectralSequence.hom_ext
    intro r hr
    change (filteredComplexCanonicalMap (t ≫ t')).hom r _ = _
    rw [filteredComplexCanonicalMap_comp]
    rfl

end CategoryTheory
