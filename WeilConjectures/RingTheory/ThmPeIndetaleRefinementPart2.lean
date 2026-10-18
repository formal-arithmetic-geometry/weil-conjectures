/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ThmPeIndetaleRefinementPart1
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Supporting results for `sk-thm-pe-indetale-refinement`

Supporting results for the blueprint unit `sk-thm-pe-indetale-refinement` of `sec-proetale-
coefficients`, grouped from `PrincipalWLocalizationEvaluation`, `RetainedLocalization`,
`PrincipalWLocalizationPrimeCharts`, `PrincipalWLocalizationPoints`.
-/

@[expose] public section

/-! ### From `PrincipalWLocalizationEvaluation` -/
section
/-! # Evaluation of the principal w-localization at a prime

Source: blueprint order 1223, proof step 6
(auxiliary; not a blueprint node).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization

variable {A : Type u} [CommRing A]

/-- The unique part containing a prime. The partition property determines this choice uniquely.
Source: blueprint order 1223, steps 3 and 6
(auxiliary; not a blueprint node). -/
noncomputable def partAt (i : Index A) (x : PrimeSpectrum A) : i.parts :=
  (i.partition x).choose

/-- The chosen part contains the prime, by the partition property.
Source: blueprint order 1223 (auxiliary; not a blueprint node). -/
theorem mem_partAt (i : Index A) (x : PrimeSpectrum A) : x ∈ (partAt i x).val :=
  (i.partition x).choose_spec.1

/-- Uniqueness identifies the part containing the prime.
Source: blueprint order 1223 (auxiliary; not a blueprint node). -/
theorem partAt_eq (i : Index A) (x : PrimeSpectrum A) (E : i.parts)
    (h : x ∈ E.val) : partAt i x = E :=
  ((i.partition x).choose_spec.2 E h).symm

/-- The selected part of a refinement has as parent the selected original part.
Source: blueprint order 1223 (auxiliary; not a blueprint node). -/
theorem parent_partAt {i j : Index A} (h : i ≤ j) (x : PrimeSpectrum A) :
    parent h (partAt j x) = partAt i x := by
  apply (partAt_eq i x _ _).symm
  exact (Classical.choose_spec (h (partAt j x))).1 (mem_partAt j x)

/-- The canonical map from the localization at a part's denominator to the localization at a
prime in that part. Its denominator is outside the prime, hence becomes a unit.
Source: blueprint order 1223, step 6
(auxiliary; not a blueprint node). -/
noncomputable def partToLocal (i : Index A) (x : PrimeSpectrum A) :
    Localization.Away (i.denominator (partAt i x)) →ₐ[A] Localization.AtPrime x.asIdeal :=
  IsLocalization.Away.liftAlgHom _ (f := Algebra.ofId A _)
    ((IsLocalization.AtPrime.isUnit_to_map_iff _ x.asIdeal _).mpr
      (i.nonvanishing (partAt i x) (mem_partAt i x)))

/-- Evaluate a stage on its unique part containing the prime.
Source: blueprint order 1223, step 6
(auxiliary; not a blueprint node). -/
noncomputable def stageEvaluation (i : Index A) (x : PrimeSpectrum A) :
    Stage i →ₐ[A] Localization.AtPrime x.asIdeal :=
  (partToLocal i x).comp
    (Pi.evalAlgHom A (fun E : i.parts ↦ Localization.Away (i.denominator E)) (partAt i x))

/-- Evaluation commutes with refinement: the child containing the point has as its parent
precisely the old part containing the point, and localization maps are unique on `A`.
Source: blueprint order 1223 (auxiliary; not a blueprint node). -/
theorem stageEvaluation_transition {i j : Index A} (h : i ≤ j)
    (x : PrimeSpectrum A) :
    (stageEvaluation j x).comp (transition h) = stageEvaluation i x := by
  have hp := parent_partAt h x
  ext b
  change (partToLocal j x)
      ((IsLocalization.Away.liftAlgHom (i.denominator (parent h (partAt j x)))
        (f := Algebra.ofId A (Localization.Away (j.denominator (partAt j x))))
        (IsLocalization.Away.isUnit_of_dvd _ (parent_dvd h (partAt j x))))
          (b (parent h (partAt j x)))) = (partToLocal i x) (b (partAt i x))
  have hsame (E F : i.parts) (hEF : E = F)
      (f : Localization.Away (i.denominator E) →ₐ[A] Localization.AtPrime x.asIdeal)
      (g : Localization.Away (i.denominator F) →ₐ[A] Localization.AtPrime x.asIdeal) :
      f (b E) = g (b F) := by
    subst F
    have hfg : f = g := by
      apply IsLocalization.algHom_ext (Submonoid.powers (i.denominator E))
      ext
    rw [hfg]
  exact hsame _ _ hp
    ((partToLocal j x).comp
      (IsLocalization.Away.liftAlgHom (i.denominator (parent h (partAt j x)))
        (f := Algebra.ofId A (Localization.Away (j.denominator (partAt j x))))
        (IsLocalization.Away.isUnit_of_dvd _ (parent_dvd h (partAt j x)))))
    (partToLocal i x)

/-- The cocone of stage evaluations. It is concrete and uses only the localization universal
property, rather than a choice of a map from an existence statement.
Source: blueprint order 1223, step 6
(auxiliary; not a blueprint node). -/
noncomputable def evaluationCocone (x : PrimeSpectrum A) : Cocone (diagram (A := A)) where
  pt := CommAlgCat.of A (Localization.AtPrime x.asIdeal)
  ι :=
    { app i := CommAlgCat.ofHom (stageEvaluation i x)
      naturality {i j} h := by
        apply CommAlgCat.hom_ext
        exact stageEvaluation_transition h.le x }

/-- The canonical evaluation map to `A_x`, induced by the explicit stage maps.
Source: blueprint order 1223, step 6
(auxiliary; not a blueprint node). -/
noncomputable def evaluation (x : PrimeSpectrum A) :
    algebra A →ₐ[A] Localization.AtPrime x.asIdeal :=
  (colimit.desc diagram (evaluationCocone x)).hom

/-- Evaluation on a colimit representative is evaluation at its selected coordinate.
Source: blueprint order 1223 (auxiliary; not a blueprint node). -/
theorem evaluation_ι (x : PrimeSpectrum A) (i : Index A) (b : Stage i) :
    evaluation x ((colimit.ι diagram i).hom b) = stageEvaluation i x b :=
  DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (colimit.ι_desc (evaluationCocone x) i)) b

/-- The partition by a constructible set and its complement, omitting empty parts. The chosen
set has denominator `f`, and its complement has denominator one.
Source: blueprint order 1223, steps 5 and 6
(auxiliary; not a blueprint node). -/
noncomputable def cutIndex (E : Set (PrimeSpectrum A)) (hE : Topology.IsConstructible E)
    (f : A) (hf : E ⊆ PrimeSpectrum.basicOpen f) : Index A := by
  classical
  refine
    { parts := ({E, Eᶜ} : Finset (Set (PrimeSpectrum A))).filter Set.Nonempty
      nonempty := fun F hF ↦ (Finset.mem_filter.mp hF).2
      constructible := ?_
      partition := ?_
      denominator := fun F ↦ if F.val = E then f else 1
      nonvanishing := ?_ }
  · intro F hF
    rcases Finset.mem_insert.mp (Finset.mem_filter.mp hF).1 with rfl | hF
    · exact hE
    · rw [Finset.mem_singleton] at hF
      simpa only [hF] using hE.compl
  · intro p
    by_cases hp : p ∈ E
    · let F : ({E, Eᶜ} : Finset _).filter Set.Nonempty :=
        ⟨E, Finset.mem_filter.mpr ⟨by simp, ⟨p, hp⟩⟩⟩
      refine ⟨F, hp, ?_⟩
      intro G hG
      apply Subtype.ext
      rcases Finset.mem_insert.mp (Finset.mem_filter.mp G.property).1 with h | h
      · exact h
      · rw [Finset.mem_singleton] at h
        exact False.elim ((h ▸ hG) hp)
    · let F : ({E, Eᶜ} : Finset _).filter Set.Nonempty :=
        ⟨Eᶜ, Finset.mem_filter.mpr ⟨by simp, ⟨p, hp⟩⟩⟩
      refine ⟨F, hp, ?_⟩
      intro G hG
      apply Subtype.ext
      rcases Finset.mem_insert.mp (Finset.mem_filter.mp G.property).1 with h | h
      · exact False.elim (hp (h ▸ hG))
      · exact Finset.mem_singleton.mp h
  · intro F
    split_ifs with h
    · intro p hp
      apply hf
      simpa only [h] using hp
    · simpa only [PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top] using
        Set.subset_univ F.val

/-- The evaluation map is onto. Write an element of `A_x` as `a/s`, cut by `D(s)` and its
complement, and put that fraction on `D(s)`; the other coordinate is immaterial. Evaluation
takes this tuple to the required fraction. The denominator may vary with the index.
Source: blueprint order 1223, proof step 6
(auxiliary; not a blueprint node). -/
theorem evaluation_surjective (x : PrimeSpectrum A) : Function.Surjective (evaluation x) := by
  classical
  intro z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq x.asIdeal.primeCompl z
  let E : Set (PrimeSpectrum A) := PrimeSpectrum.basicOpen (s : A)
  have hE : Topology.IsConstructible E :=
    (PrimeSpectrum.isCompact_basicOpen (s : A)).isConstructible
      (PrimeSpectrum.basicOpen (s : A)).isOpen
  let i := cutIndex E hE s Set.Subset.rfl
  have hxE : x ∈ E := s.property
  let F : i.parts := ⟨E, Finset.mem_filter.mpr ⟨by simp, ⟨x, hxE⟩⟩⟩
  have hp : partAt i x = F := partAt_eq i x F hxE
  have hd : i.denominator (partAt i x) = (s : A) := by
    rw [hp]
    simp [i, F, cutIndex]
  let b : Stage i := fun G ↦
    algebraMap A _ a * IsLocalization.Away.invSelf (i.denominator G)
  refine ⟨(colimit.ι diagram i).hom b, ?_⟩
  rw [evaluation_ι, IsLocalization.eq_mk'_iff_mul_eq]
  change partToLocal i x (b (partAt i x)) * algebraMap A _ (s : A) = _
  rw [← hd, ← (partToLocal i x).commutes, ← map_mul]
  change partToLocal i x
    ((algebraMap A _ a * IsLocalization.Away.invSelf (i.denominator (partAt i x))) *
      algebraMap A _ (i.denominator (partAt i x))) = _
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf _),
    IsLocalization.Away.mul_invSelf, mul_one, AlgHom.commutes]

end PrincipalWLocalization
end

/-! ### From `RetainedLocalization` -/
section
/-! # Retaining a closed subset in the principal w-localization

Source: blueprint, proper base change, Retaining a closed subset, order 1224
(blueprint: def-weil-pbc-retained-localization).

Selectors are constructed at the two-part partition into a constructible set and its
complement, omitting empty parts. Their localizations form a reverse-inclusion diagram.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization.Retained

variable {R : Type u} [CommRing R]

open Classical in
/-- The nonempty parts of the partition into `E` and its complement.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def parts (E : Set (PrimeSpectrum R)) : Finset (Set (PrimeSpectrum R)) :=
  Finset.filter Set.Nonempty ({E, Eᶜ} : Finset (Set (PrimeSpectrum R)))

/-- The two-part partition satisfies the index conditions with denominator one.
Proof: filter out the empty sets; constructibility is closed under complement; each point
lies in exactly one of `E` and its complement; `D(1)` is the whole spectrum.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem parts_valid (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    (∀ F ∈ parts E, Set.Nonempty F) ∧
    (∀ F ∈ parts E, Topology.IsConstructible F) ∧
    (∀ p : PrimeSpectrum R, ∃! F : parts E, p ∈ F.val) ∧
    (∀ F : parts E, F.val ⊆ PrimeSpectrum.basicOpen (1 : R)) := by
  classical
  have mem_parts (F : Set (PrimeSpectrum R)) :
      F ∈ parts E ↔ (F = E ∨ F = Eᶜ) ∧ F.Nonempty := by
    simp [parts]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F hF
    exact ((mem_parts F).mp hF).2
  · intro F hF
    rcases ((mem_parts F).mp hF).1 with rfl | rfl
    · exact hE
    · exact hE.compl
  · intro p
    by_cases hp : p ∈ E
    · refine ⟨⟨E, (mem_parts E).mpr ⟨Or.inl rfl, ⟨p, hp⟩⟩⟩, hp, ?_⟩
      intro F hF
      apply Subtype.ext
      rcases ((mem_parts F.val).mp F.property).1 with he | he
      · exact he
      · exact False.elim ((he ▸ hF) hp)
    · refine ⟨⟨Eᶜ, (mem_parts Eᶜ).mpr ⟨Or.inr rfl, ⟨p, hp⟩⟩⟩, hp, ?_⟩
      intro F hF
      apply Subtype.ext
      rcases ((mem_parts F.val).mp F.property).1 with he | he
      · exact False.elim (hp (he ▸ hF))
      · exact he
  · intro F p hp
    simp

/-- The partition index used to construct the selector, with constant denominator one.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def selectorIndex (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    Index R where
  parts := parts E
  nonempty := (parts_valid E hE).1
  constructible := (parts_valid E hE).2.1
  partition := (parts_valid E hE).2.2.1
  denominator := fun _ ↦ 1
  nonvanishing := (parts_valid E hE).2.2.2

open Classical in
/-- The image in `R^w` of the stage element which is one on `E` and zero on its complement.
This specifies the selector by actual data, including when `E` or the spectrum is empty.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def selector (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    algebra R :=
  (colimit.ι (diagram (A := R)) (selectorIndex E hE)).hom
    (fun F ↦ if F.val ⊆ E then 1 else 0)

/-- The selector is idempotent. Proof: each stage coordinate is zero or one, so its square
is itself; the colimit inclusion preserves multiplication.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem selector_idempotent (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    IsIdempotentElem (selector E hE) := by
  classical
  apply IsIdempotentElem.map
  change (fun F : (selectorIndex E hE).parts ↦
    if F.val ⊆ E then (1 : Localization.Away ((selectorIndex E hE).denominator F))
    else 0) * _ = _
  funext F
  simp only [Pi.mul_apply]
  split_ifs <;> simp

/-- Constructible neighbourhoods of `T`, ordered by reverse inclusion.
Here neighbourhood means a constructible superset, exactly as in the source.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
abbrev Neighborhood (T : Set (PrimeSpectrum R)) :=
  OrderDual {E : Set (PrimeSpectrum R) // Topology.IsConstructible E ∧ T ⊆ E}

/-- The neighbourhood index is filtered. Proof: the whole spectrum is a neighbourhood;
the intersection of two neighbourhoods contains `T`, is constructible, and is an upper
bound for reverse inclusion. The preorder has at most one arrow between any two objects.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem neighborhood_isFiltered (T : Set (PrimeSpectrum R)) : IsFiltered (Neighborhood T) := by
  refine { cocone_objs := ?_, cocone_maps := ?_, nonempty := ?_ }
  · intro E F
    let G : Neighborhood T :=
      ⟨E.val ∩ F.val, E.property.1.inter F.property.1,
        fun p hp ↦ ⟨E.property.2 hp, F.property.2 hp⟩⟩
    exact ⟨G, homOfLE Set.inter_subset_left, homOfLE Set.inter_subset_right, trivial⟩
  · intro E F f g
    exact ⟨F, 𝟙 F, Subsingleton.elim _ _⟩
  · exact ⟨⟨Set.univ, Topology.IsConstructible.univ, Set.subset_univ T⟩⟩

attribute [instance] neighborhood_isFiltered

open Classical in
private theorem transition_selector (E : Set (PrimeSpectrum R))
    (hE : Topology.IsConstructible E) {j : Index R} (h : selectorIndex E hE ≤ j) :
    PrincipalWLocalization.transition h (fun P ↦ if P.val ⊆ E then 1 else 0) =
      (fun Q ↦ if Q.val ⊆ E then 1 else 0) := by
  classical
  funext Q
  have hsub : Q.val ⊆ (parent h Q).val := (Classical.choose_spec (h Q)).1
  have hiff : (parent h Q).val ⊆ E ↔ Q.val ⊆ E := by
    refine ⟨fun hP ↦ hsub.trans hP, ?_⟩
    intro hQ
    have hmem : (parent h Q).val ∈ parts E := (parent h Q).property
    have hcases : (parent h Q).val = E ∨ (parent h Q).val = Eᶜ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton]
        using (Finset.mem_filter.mp hmem).1
    rcases hcases with he | he
    · rw [he]
    · obtain ⟨p, hp⟩ := j.nonempty Q.val Q.property
      exact False.elim ((he ▸ hsub hp) (hQ hp))
  simp only [PrincipalWLocalization.transition, AlgHom.pi_apply, AlgHom.comp_apply,
    Pi.evalAlgHom_apply]
  simp only [hiff]
  split_ifs <;> simp

/-- For `F ⊆ E`, the selector of `E` is a unit after localizing at the selector of `F`.
Proof: refine both two-part partitions by their nonempty intersections with denominator one.
The coordinate selectors satisfy `e_E * e_F = e_F`, hence so do their colimit images.
After inverting `e_F`, the image of `e_E` is one and thus a unit.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem selector_isUnit {E F : Set (PrimeSpectrum R)}
    (hE : Topology.IsConstructible E) (hF : Topology.IsConstructible F) (hFE : F ⊆ E) :
    IsUnit (algebraMap (algebra R) (Localization.Away (selector F hF)) (selector E hE)) := by
  classical
  obtain ⟨j, f, g, _⟩ :=
    IsFilteredOrEmpty.cocone_objs (selectorIndex E hE) (selectorIndex F hF)
  have he : selector E hE = (colimit.ι (diagram (A := R)) j).hom
      (fun Q ↦ if Q.val ⊆ E then 1 else 0) := by
    rw [← transition_selector E hE f.le]
    exact (ConcreteCategory.congr_hom (colimit.w (diagram (A := R)) f) _).symm
  have hf : selector F hF = (colimit.ι (diagram (A := R)) j).hom
      (fun Q ↦ if Q.val ⊆ F then 1 else 0) := by
    rw [← transition_selector F hF g.le]
    exact (ConcreteCategory.congr_hom (colimit.w (diagram (A := R)) g) _).symm
  let c : Stage j →ₐ[R] PrincipalWLocalization.algebra R :=
    (colimit.ι (diagram (A := R)) j).hom
  have hmul : selector E hE * selector F hF = selector F hF := by
    rw [he, hf]
    change c _ * c _ = c _
    rw [← map_mul]
    apply congrArg c
    funext Q
    simp only [Pi.mul_apply]
    by_cases hQ : Q.val ⊆ F
    · simp [hQ, hQ.trans hFE]
    · simp [hQ]
  exact IsLocalization.Away.isUnit_of_dvd (selector F hF)
    ⟨selector F hF, hmul.symm⟩

/-- The transition is the unique `R^w`-algebra map between the selector localizations.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def transition {T : Set (PrimeSpectrum R)} {E F : Neighborhood T} (h : E ≤ F) :
    Localization.Away (selector E.val E.property.1) →ₐ[algebra R]
      Localization.Away (selector F.val F.property.1) :=
  IsLocalization.Away.liftAlgHom (selector E.val E.property.1)
    (f := Algebra.ofId (algebra R) (Localization.Away (selector F.val F.property.1)))
    (selector_isUnit E.property.1 F.property.1 h)

/-- Identity transitions are identities by uniqueness of maps out of localization.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem transition_id {T : Set (PrimeSpectrum R)} (E : Neighborhood T) :
    transition (le_refl E) = AlgHom.id (algebra R)
      (Localization.Away (selector E.val E.property.1)) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (selector E.val E.property.1))
  ext

/-- Transitions compose: both maps agree on `R^w`, so localization uniqueness identifies them.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
theorem transition_comp {T : Set (PrimeSpectrum R)} {E F G : Neighborhood T}
    (hEF : E ≤ F) (hFG : F ≤ G) :
    transition (le_trans hEF hFG) = (transition hFG).comp (transition hEF) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (selector E.val E.property.1))
  ext

/-- The reverse-inclusion diagram of localizations at the constructible selectors.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def localizationDiagram (T : Set (PrimeSpectrum R)) :
    Neighborhood T ⥤ CommAlgCat.{u} (algebra R) where
  obj E := CommAlgCat.of (algebra R) (Localization.Away (selector E.val E.property.1))
  map h := CommAlgCat.ofHom (transition h.le)
  map_id E := congrArg CommAlgCat.ofHom (transition_id E)
  map_comp h g := congrArg CommAlgCat.ofHom (transition_comp h.le g.le)

/-- The retained localization `R_[T]` is the colimit of `(R^w)[1/e_E]` over all constructible
supersets `E` of the closed set `T`, with reverse-inclusion transition maps.
Source: blueprint order 1224 (blueprint: def-weil-pbc-retained-localization). -/
noncomputable def algebra (T : Set (PrimeSpectrum R)) (_hT : IsClosed T) :
    CommAlgCat.{u} (PrincipalWLocalization.algebra R) :=
  colimit (localizationDiagram T)

end PrincipalWLocalization.Retained
end

/-! ### From `PrincipalWLocalizationPrimeCharts` -/
section
/-! # Prime charts of the principal w-localization

Source: blueprint order 1223, proof steps 1–7
(auxiliary; not a blueprint node).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrincipalWLocalization

variable {A : Type u} [CommRing A]

/-- The prime over `(x,y)` is the inverse image of the prime of `A_x` contracting to `y`.
This uses the explicit evaluation map and the localization prime correspondence.
Source: blueprint order 1223, step 3
(auxiliary; not a blueprint node). -/
noncomputable def pairPoint (p :
    {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal}) :
    PrimeSpectrum (algebra A) :=
  PrimeSpectrum.comap (evaluation p.val.1).toRingHom
    ((IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime p.val.1.asIdeal) p.val.1.asIdeal).symm ⟨p.val.2, p.property⟩)

private theorem evaluation_comp (x : PrimeSpectrum A) :
    (evaluation x).toRingHom.comp (algebraMap A (algebra A)) =
      algebraMap A (Localization.AtPrime x.asIdeal) := by
  ext a
  exact (evaluation x).commutes a

private theorem pairPoint_contraction (p :
    {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal}) :
    PrimeSpectrum.comap (algebraMap A (algebra A)) (pairPoint p) = p.val.2 := by
  unfold pairPoint
  rw [← PrimeSpectrum.comap_comp_apply, evaluation_comp]
  exact congrArg Subtype.val
    ((IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime p.val.1.asIdeal) p.val.1.asIdeal).apply_symm_apply
        ⟨p.val.2, p.property⟩)

private noncomputable def stagePoint (q : PrimeSpectrum (algebra A)) (i : Index A) :
    (E : i.parts) × PrimeSpectrum (Localization.Away (i.denominator E)) :=
  (Equiv.ofBijective
    (PrimeSpectrum.sigmaToPi (fun E : i.parts ↦ Localization.Away (i.denominator E)))
    (PrimeSpectrum.sigmaToPi_bijective _)).symm
      (PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom q)

private theorem stagePoint_spec (q : PrimeSpectrum (algebra A)) (i : Index A) :
    PrimeSpectrum.sigmaToPi (fun E : i.parts ↦ Localization.Away (i.denominator E))
      (stagePoint q i) =
      PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom q :=
  (Equiv.ofBijective _ (PrimeSpectrum.sigmaToPi_bijective
    (fun E : i.parts ↦ Localization.Away (i.denominator E)))).apply_symm_apply _

private theorem stagePoint_parent (q : PrimeSpectrum (algebra A)) {i j : Index A}
    (h : i ≤ j) : parent h (stagePoint q j).1 = (stagePoint q i).1 := by
  let F := (stagePoint q j).1
  let p := (stagePoint q j).2
  let f : Localization.Away (i.denominator (parent h F)) →ₐ[A]
      Localization.Away (j.denominator F) :=
    IsLocalization.Away.liftAlgHom _ (f := Algebra.ofId A _)
      (IsLocalization.Away.isUnit_of_dvd _ (parent_dvd h F))
  have hh : PrimeSpectrum.sigmaToPi
      (fun E : i.parts ↦ Localization.Away (i.denominator E))
      ⟨parent h F, PrimeSpectrum.comap f.toRingHom p⟩ =
      PrimeSpectrum.comap (transition h).toRingHom
        (PrimeSpectrum.sigmaToPi (fun E : j.parts ↦ Localization.Away (j.denominator E))
          (stagePoint q j)) := by
    rw [PrimeSpectrum.sigmaToPi_apply, PrimeSpectrum.sigmaToPi_apply,
      ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
    rfl
  rw [stagePoint_spec, ← PrimeSpectrum.comap_comp_apply] at hh
  have hw : (colimit.ι diagram j).hom.toRingHom.comp (transition h).toRingHom =
      (colimit.ι diagram i).hom.toRingHom := by
    exact congrArg (fun f ↦ f.hom.toRingHom) (colimit.w diagram (homOfLE h))
  rw [hw, ← stagePoint_spec] at hh
  exact congrArg Sigma.fst ((PrimeSpectrum.sigmaToPi_bijective _).injective hh)

private theorem stagePoint_contraction (q : PrimeSpectrum (algebra A)) (i : Index A) :
    PrimeSpectrum.comap (algebraMap A
      (Localization.Away (i.denominator (stagePoint q i).1))) (stagePoint q i).2 =
      PrimeSpectrum.comap (algebraMap A (algebra A)) q := by
  calc
    _ = PrimeSpectrum.comap (algebraMap A (Stage i))
        (PrimeSpectrum.sigmaToPi
          (fun E : i.parts ↦ Localization.Away (i.denominator E)) (stagePoint q i)) := by
      rw [PrimeSpectrum.sigmaToPi_apply, ← PrimeSpectrum.comap_comp_apply]
      rfl
    _ = PrimeSpectrum.comap (algebraMap A (Stage i))
        (PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom q) := by
      rw [stagePoint_spec]
    _ = _ := by
      rw [← PrimeSpectrum.comap_comp_apply]
      congr 1
      ext a
      exact (colimit.ι diagram i).hom.commutes a

private theorem stagePoint_subset (q : PrimeSpectrum (algebra A)) {i j : Index A}
    (h : i ≤ j) : (stagePoint q j).1.val ⊆ (stagePoint q i).1.val := by
  have hh := (Classical.choose_spec (h (stagePoint q j).1)).1
  change (stagePoint q j).1.val ⊆ (parent h (stagePoint q j).1).val at hh
  rwa [stagePoint_parent q h] at hh

private theorem exists_selected_point (q : PrimeSpectrum (algebra A)) :
    ∃ x : PrimeSpectrum A, ∀ i : Index A, partAt i x = (stagePoint q i).1 := by
  classical
  let S : Index A → Set (WithConstructibleTopology (PrimeSpectrum A)) :=
    fun i ↦ WithTopology.ofTopology ⁻¹' (stagePoint q i).1.val
  have hclosed (i : Index A) : IsClosed (S i) := by
    rw [WithConstructibleTopology.isClosed_iff]
    exact (i.constructible _ (stagePoint q i).1.property).isClopen_constructibleTopology.1
  have hnonempty (i : Index A) : (S i).Nonempty := by
    obtain ⟨x, hx⟩ := i.nonempty _ (stagePoint q i).1.property
    exact ⟨WithTopology.toTopology _ x, hx⟩
  have hdir : Directed (· ⊇ ·) S := by
    intro i j
    refine ⟨IsFiltered.max i j, ?_, ?_⟩
    · intro x hx
      exact stagePoint_subset q (IsFiltered.leftToMax i j).le hx
    · intro x hx
      exact stagePoint_subset q (IsFiltered.rightToMax i j).le hx
  have : Nonempty (Index A) := IsFiltered.nonempty
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S
    hdir hnonempty (fun i ↦ (hclosed i).isCompact) hclosed
  refine ⟨x.ofTopology, fun i ↦ partAt_eq i _ _ (Set.mem_iInter.mp hx i)⟩

private theorem cutIndex_partAt (E : Set (PrimeSpectrum A))
    (hE : Topology.IsConstructible E) (f : A) (hf : E ⊆ PrimeSpectrum.basicOpen f)
    (x : PrimeSpectrum A) :
    (partAt (cutIndex E hE f hf) x).val = E ↔ x ∈ E := by
  classical
  constructor
  · intro h
    exact h ▸ mem_partAt _ x
  · intro hx
    let F : (cutIndex E hE f hf).parts :=
      ⟨E, Finset.mem_filter.mpr ⟨by simp, ⟨x, hx⟩⟩⟩
    exact congrArg Subtype.val (partAt_eq _ x F hx)

private theorem contraction_le_selected (q : PrimeSpectrum (algebra A)) (x : PrimeSpectrum A)
    (hx : ∀ i : Index A, partAt i x = (stagePoint q i).1) :
    (PrimeSpectrum.comap (algebraMap A (algebra A)) q).asIdeal ≤ x.asIdeal := by
  intro f hfy
  by_contra hfx
  let E : Set (PrimeSpectrum A) := PrimeSpectrum.basicOpen f
  have hE : Topology.IsConstructible E :=
    (PrimeSpectrum.isCompact_basicOpen f).isConstructible (PrimeSpectrum.basicOpen f).isOpen
  let i := cutIndex E hE f Set.Subset.rfl
  have hpart : (stagePoint q i).1.val = E := by
    rw [← hx i]
    exact (cutIndex_partAt E hE f Set.Subset.rfl x).mpr hfx
  have hden : i.denominator (stagePoint q i).1 = f := by
    change (if (stagePoint q i).1.val = E then f else 1) = f
    rw [if_pos hpart]
  have hnot : i.denominator (stagePoint q i).1 ∉
      (PrimeSpectrum.comap (algebraMap A (algebra A)) q).asIdeal := by
    rw [← stagePoint_contraction q i]
    change algebraMap A (Localization.Away (i.denominator (stagePoint q i).1))
      (i.denominator (stagePoint q i).1) ∉ (stagePoint q i).2.asIdeal
    exact Ideal.notMem_of_isUnit _
      (IsLocalization.Away.algebraMap_isUnit (i.denominator (stagePoint q i).1))
  exact hnot (hden.symm ▸ hfy)

open Classical in
private noncomputable def characteristic (E : Set (PrimeSpectrum A))
    (hE : Topology.IsConstructible E) : algebra A :=
  let i := cutIndex E hE 1 (by simp)
  (colimit.ι diagram i).hom (fun F ↦ if F.val = E then 1 else 0)

open Classical in
private theorem evaluation_characteristic (E : Set (PrimeSpectrum A))
    (hE : Topology.IsConstructible E) (x : PrimeSpectrum A) :
    evaluation x (characteristic E hE) = if x ∈ E then 1 else 0 := by
  classical
  rw [characteristic, evaluation_ι]
  change partToLocal _ x (if (partAt _ x).val = E then 1 else 0) = _
  simp only [cutIndex_partAt]
  split_ifs <;> simp

private theorem pairPoint_characteristic (E : Set (PrimeSpectrum A))
    (hE : Topology.IsConstructible E)
    (p : {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal}) :
    characteristic E hE ∉ (pairPoint p).asIdeal ↔ p.val.1 ∈ E := by
  classical
  let P := (IsLocalization.AtPrime.primeSpectrumOrderIso
    (Localization.AtPrime p.val.1.asIdeal) p.val.1.asIdeal).symm ⟨p.val.2, p.property⟩
  change evaluation p.val.1 (characteristic E hE) ∉ P.asIdeal ↔ _
  rw [evaluation_characteristic]
  split_ifs with hx
  · exact iff_of_true P.isPrime.one_notMem hx
  · exact iff_of_false (fun h ↦ h P.asIdeal.zero_mem) hx

private theorem stagePoint_pairPoint
    (p : {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal})
    (i : Index A) : (stagePoint (pairPoint p) i).1 = partAt i p.val.1 := by
  let P := (IsLocalization.AtPrime.primeSpectrumOrderIso
    (Localization.AtPrime p.val.1.asIdeal) p.val.1.asIdeal).symm ⟨p.val.2, p.property⟩
  have hh : PrimeSpectrum.sigmaToPi
      (fun E : i.parts ↦ Localization.Away (i.denominator E))
      ⟨partAt i p.val.1, PrimeSpectrum.comap (partToLocal i p.val.1).toRingHom P⟩ =
      PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom (pairPoint p) := by
    rw [PrimeSpectrum.sigmaToPi_apply, ← PrimeSpectrum.comap_comp_apply]
    unfold pairPoint
    rw [← PrimeSpectrum.comap_comp_apply]
    have hcomp : (partToLocal i p.val.1).toRingHom.comp
        (Pi.evalRingHom (fun E : i.parts ↦ Localization.Away (i.denominator E))
          (partAt i p.val.1)) =
        (evaluation p.val.1).toRingHom.comp (colimit.ι diagram i).hom.toRingHom := by
      apply RingHom.ext
      intro b
      exact (evaluation_ι p.val.1 i b).symm
    rw [hcomp]
  rw [← stagePoint_spec] at hh
  exact (congrArg Sigma.fst ((PrimeSpectrum.sigmaToPi_bijective _).injective hh)).symm

private theorem stagePoint_eq_of_same_part (q r : PrimeSpectrum (algebra A)) (i : Index A)
    (hpart : (stagePoint q i).1 = (stagePoint r i).1)
    (hcontraction : PrimeSpectrum.comap (algebraMap A (algebra A)) q =
      PrimeSpectrum.comap (algebraMap A (algebra A)) r) :
    stagePoint q i = stagePoint r i := by
  have hcq := stagePoint_contraction q i
  have hcr := stagePoint_contraction r i
  generalize hq : stagePoint q i = Q at *
  generalize hr : stagePoint r i = R at *
  rcases Q with ⟨E, P⟩
  rcases R with ⟨F, Q⟩
  dsimp only at hpart hcq hcr
  subst F
  have heq : P = Q := PrimeSpectrum.localization_comap_injective
    (Localization.Away (i.denominator E)) (Submonoid.powers (i.denominator E))
      (hcq.trans (hcontraction.trans hcr.symm))
  rw [heq]

private theorem eq_of_stagePoint_eq (q r : PrimeSpectrum (algebra A))
    (h : ∀ i : Index A, stagePoint q i = stagePoint r i) : q = r := by
  apply PrimeSpectrum.ext
  ext a
  obtain ⟨i, b, rfl⟩ := Concrete.isColimit_exists_rep diagram (colimit.isColimit diagram) a
  change b ∈ (PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom q).asIdeal ↔
    b ∈ (PrimeSpectrum.comap (colimit.ι diagram i).hom.toRingHom r).asIdeal
  rw [← stagePoint_spec, ← stagePoint_spec, h]

private theorem pairPoint_surjective : Function.Surjective (pairPoint (A := A)) := by
  intro q
  obtain ⟨x, hx⟩ := exists_selected_point q
  let p : {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal} :=
    ⟨(x, PrimeSpectrum.comap (algebraMap A (algebra A)) q), contraction_le_selected q x hx⟩
  refine ⟨p, eq_of_stagePoint_eq _ _ fun i ↦ ?_⟩
  apply stagePoint_eq_of_same_part
  · exact (stagePoint_pairPoint p i).trans (hx i)
  · exact pairPoint_contraction p

private theorem pairPoint_injective : Function.Injective (pairPoint (A := A)) := by
  intro p r hpr
  apply Subtype.ext
  have hsecond : p.val.2 = r.val.2 := by
    rw [← pairPoint_contraction, ← pairPoint_contraction, hpr]
  apply Prod.ext _ hsecond
  apply PrimeSpectrum.ext
  ext f
  have hE : Topology.IsConstructible (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) :=
    (PrimeSpectrum.isCompact_basicOpen f).isConstructible (PrimeSpectrum.basicOpen f).isOpen
  have hh := (pairPoint_characteristic _ hE p).symm.trans
    ((congrArg (fun q : PrimeSpectrum (algebra A) ↦
      characteristic _ hE ∉ q.asIdeal) hpr).to_iff.trans (pairPoint_characteristic _ hE r))
  exact not_iff_not.mp hh

/-- The prime-pair correspondence, its contraction, the continuous patch coordinate, and the
closed affine charts of its fibres.

Source: blueprint order 1223, proof steps 1–7
(auxiliary; not a blueprint node).
Proof:
1. A prime of each finite product selects exactly one factor, by the finite-product spectrum
bijection. Compatibility of the colimit injections makes the selected parts refine each other.
2. The selected constructible parts are closed in the compact patch space. They form a directed
nonempty family, so they have a common point `x`.
3. For `f` outside `x`, use the cut by `D(f)` with denominator `f`. The selected factor inverts
`f`, so the contracted prime `y` does not contain `f`. Thus `y` is contained in `x`.
4. The prime over `(x,y)` is obtained from the explicit evaluation to `A_x` and the localization
prime correspondence. Its selected part at each stage is the part containing `x`. Two primes
with the same selected parts and the same contraction coincide, since localization primes are
determined by contraction and every colimit element has a stage representative.
5. The characteristic tuple of any constructible set evaluates to one at its points and zero
elsewhere. Thus it distinguishes the first coordinates. Contraction distinguishes the second,
so the correspondence is bijective.
6. The preimage of a constructible set under the first-coordinate map is the basic open of its
characteristic element. In particular the preimages of the patch subbasis are open, proving
continuity.
7. The evaluation map to `A_x` is surjective by `evaluation_surjective`, so its spectrum map is a
closed immersion. The prime correspondence identifies its range exactly with first coordinate
`x`, by the localization prime correspondence. This includes the zero ring: then no prime is
present and the statements about individual fibres are vacuous. -/
theorem primeCharts (A : Type u) [CommRing A] :
    ∃ e : PrimeSpectrum (algebra A) ≃
      {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal},
      (∀ q, PrimeSpectrum.comap (algebraMap A (algebra A)) q = (e q).val.2) ∧
      (@Continuous (PrimeSpectrum (algebra A)) (PrimeSpectrum A) inferInstance
        (constructibleTopology (PrimeSpectrum A)) (fun q ↦ (e q).val.1)) ∧
      (∀ x : PrimeSpectrum A,
        ∃ ρ : algebra A →ₐ[A] Localization.AtPrime x.asIdeal,
          IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ.toRingHom)) ∧
          Set.range (PrimeSpectrum.comap ρ.toRingHom) = {q | (e q).val.1 = x}) := by
  classical
  let d := Equiv.ofBijective (pairPoint (A := A)) ⟨pairPoint_injective, pairPoint_surjective⟩
  let e := d.symm
  have hpq (q : PrimeSpectrum (algebra A)) : pairPoint (e q) = q := d.apply_symm_apply q
  have hep (p : {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal}) :
      e (pairPoint p) = p := d.symm_apply_apply p
  refine ⟨e, ?_, ?_, ?_⟩
  · intro q
    rw [← hpq q, pairPoint_contraction, hep]
  · have hchar (E : Set (PrimeSpectrum A)) (hE : Topology.IsConstructible E)
        (q : PrimeSpectrum (algebra A)) :
        characteristic E hE ∉ q.asIdeal ↔ (e q).val.1 ∈ E := by
      rw [← hpq q]
      exact (pairPoint_characteristic E hE (e q)).trans (by rw [hep])
    change @Continuous _ _ _ (TopologicalSpace.generateFrom _) (fun q ↦ (e q).val.1)
    rw [continuous_generateFrom_iff]
    intro E hE
    have hc : Topology.IsConstructible E := by
      rcases hE with hE | hE
      · exact hE.2.isConstructible hE.1
      · have hh := (hE.2.isConstructible hE.1.isOpen_compl).compl
        simpa only [compl_compl] using hh
    have hpre : (fun q ↦ (e q).val.1) ⁻¹' E =
        (PrimeSpectrum.basicOpen (characteristic E hc) : Set (PrimeSpectrum (algebra A))) := by
      ext q
      exact (hchar E hc q).symm
    rw [hpre]
    exact (PrimeSpectrum.basicOpen _).isOpen
  · intro x
    refine ⟨evaluation x, IsClosedImmersion.spec_of_surjective _ (evaluation_surjective x), ?_⟩
    ext q
    constructor
    · rintro ⟨P, rfl⟩
      let o := IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime x.asIdeal)
        x.asIdeal
      let p : {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal} :=
        ⟨(x, (o P).val), (o P).property⟩
      have hh : pairPoint p = PrimeSpectrum.comap (evaluation x).toRingHom P := by
        change PrimeSpectrum.comap (evaluation x).toRingHom (o.symm (o P)) = _
        rw [o.symm_apply_apply]
      rw [← hh]
      change (e (pairPoint p)).val.1 = x
      rw [hep]
    · intro hq
      have hh : q ∈ Set.range (PrimeSpectrum.comap (evaluation (e q).val.1).toRingHom) :=
        ⟨_, hpq q⟩
      simpa only [Set.mem_ofPred_eq] using (hq ▸ hh)

end PrincipalWLocalization
end

/-! ### From `PrincipalWLocalizationPoints` -/
section
/-! # Points and components of the principal w-localization

Source: blueprint, proper base change, lemma "Points of the affine w-localization", order 1223
(blueprint: lem-weil-pbc-w-localization-points).
-/

universe u

open AlgebraicGeometry

namespace PrincipalWLocalization

private theorem indZariski (A : Type u) [CommRing A] :
    Algebra.IndZariski A (algebra A) := by
  let P : CategoryTheory.Limits.ColimitPresentation (Index A) (algebra A) :=
    { diag := diagram
      ι := (CategoryTheory.Limits.colimit.cocone diagram).ι
      isColimit := CategoryTheory.Limits.colimit.isColimit diagram }
  exact Algebra.IndZariski.of_colimitPresentation A (algebra A) P fun i ↦
    inferInstanceAs (Algebra.IndZariski A (Stage i))

private theorem patchT2 (A : Type u) [CommRing A] :
    T2Space (WithConstructibleTopology (PrimeSpectrum A)) := by
  classical
  refine ⟨fun x y hxy ↦ ?_⟩
  obtain ⟨f, hf⟩ : ∃ f : A,
      ¬ (f ∈ x.ofTopology.asIdeal ↔ f ∈ y.ofTopology.asIdeal) := by
    by_contra! h
    exact hxy (WithTopology.ofTopology_injective _ (PrimeSpectrum.ext (Ideal.ext h)))
  let U : Set (WithConstructibleTopology (PrimeSpectrum A)) :=
    WithTopology.ofTopology ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A))
  have hU : IsClopen U := by
    constructor
    · rw [WithConstructibleTopology.isClosed_iff]
      exact (PrimeSpectrum.isCompact_basicOpen f).isClosed_constructibleTopology_of_isOpen
        (PrimeSpectrum.basicOpen f).isOpen
    · rw [WithConstructibleTopology.isOpen_iff]
      exact (PrimeSpectrum.isCompact_basicOpen f).isOpen_constructibleTopology_of_isOpen
        (PrimeSpectrum.basicOpen f).isOpen
  by_cases hx : f ∈ x.ofTopology.asIdeal
  · have hy : f ∉ y.ofTopology.asIdeal := fun hy ↦ hf ⟨fun _ ↦ hy, fun _ ↦ hx⟩
    exact ⟨Uᶜ, U, hU.compl.isOpen, hU.isOpen, (fun h ↦ h hx), hy, disjoint_compl_left⟩
  · have hy : f ∈ y.ofTopology.asIdeal := by
      by_contra hy
      exact hf ⟨fun h ↦ (hx h).elim, fun h ↦ (hy h).elim⟩
    exact ⟨U, Uᶜ, hU.isOpen, hU.compl.isOpen, hx, (fun h ↦ h hy), disjoint_compl_right⟩

/-- The prime-pair description, local rings, component schemes, and closed points of the
finite-partition principal w-localization. The closed immersion from `Spec A_x` with image the
first-coordinate fibre equips that fibre with its canonical affine scheme structure. Its ring
map is an `A`-algebra map, so these identifications respect the structural morphism to `Spec A`.
The homeomorphism on closed points and the continuous first-coordinate map use the patch
rather than the Zariski topology on `Spec A`.

Source: blueprint order 1223 (blueprint: lem-weil-pbc-w-localization-points).
Proof:
1. The proved `primeCharts` theorem supplies the prime-pair bijection, contraction formula,
continuous first coordinate, and the closed immersion of `Spec A_x` onto its first-coordinate
fibre. Its proof selects factors of each finite stage, uses compactness of the patch spectrum,
and constructs the explicit surjective evaluation maps.
2. The colimit presentation by finite products of principal localizations is ind-Zariski.
The proved upstream `Algebra.IndZariski.bijectiveOnStalks_algebraMap` identifies the local ring
at a prime with the localization of `A` at its contraction. Its canonical local-ring map fixes
`A`, hence the inverse bijection gives the required `A`-algebra equivalence.
3. Preimages of the basic patch clopens are clopen. They force the first coordinate to be
constant on connected components and on specializations. Every point of a fibre specializes
to the image of the closed point of `Spec A_x`, namely the diagonal point `(x,x)`. Thus two
points in the same fibre have the same connected component; distinct fibres are separated by
a basic patch clopen. This proves the component formula.
4. A diagonal point is closed because it is the image of the closed point of a local spectrum
under a closed immersion. Every point specializes to its diagonal point, so these are exactly
the closed points. The complement of the diagonal is the union, over `f : A`, of the open sets
where `f` belongs to the first prime and does not belong to the contracted prime. Indeed for
`y` strictly contained in `x` one can choose `f` in `x` but outside `y`.
5. The first-coordinate bijection from the closed points to the patch spectrum is continuous.
Its domain is compact, since the closed points are closed in an affine spectrum. The patch
spectrum is Hausdorff: distinct primes are separated by the complementary patch clopens
`D(f)` and `V(f)` for an element on which they differ. A continuous bijection from a compact
space to a Hausdorff space is a homeomorphism. Its inverse is the diagonal map. The closedness
and unique closed specialization establish w-locality.
6. Ind-Zariski algebras are flat by the proved upstream API. The structural spectrum map is
surjective because of the diagonal points. Mathlib's flat-surjective-spectrum criterion gives
faithful flatness. All constructions include the empty spectrum of the zero ring; the cut
partitions omit empty parts and statements quantified over primes are then vacuous.
-/
theorem points (A : Type u) [CommRing A] :
    ∃ e : PrimeSpectrum (algebra A) ≃
        {p : PrimeSpectrum A × PrimeSpectrum A // p.2.asIdeal ≤ p.1.asIdeal},
      (∀ q : PrimeSpectrum (algebra A),
        PrimeSpectrum.comap (algebraMap A (algebra A)) q = (e q).val.2) ∧
      (∀ q : PrimeSpectrum (algebra A),
        Nonempty (Localization.AtPrime q.asIdeal ≃ₐ[A]
          Localization.AtPrime (e q).val.2.asIdeal)) ∧
      (@Continuous (PrimeSpectrum (algebra A)) (PrimeSpectrum A) inferInstance
        (constructibleTopology (PrimeSpectrum A)) (fun q ↦ (e q).val.1)) ∧
      (∀ q : PrimeSpectrum (algebra A),
        connectedComponent q = {r | (e r).val.1 = (e q).val.1}) ∧
      (∀ x : PrimeSpectrum A,
        ∃ ρ : algebra A →ₐ[A] Localization.AtPrime x.asIdeal,
          IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ.toRingHom)) ∧
          Set.range (PrimeSpectrum.comap ρ.toRingHom) = {q | (e q).val.1 = x}) ∧
      (∀ q : PrimeSpectrum (algebra A),
        q ∈ closedPoints (PrimeSpectrum (algebra A)) ↔ (e q).val.1 = (e q).val.2) ∧
      IsClosed (closedPoints (PrimeSpectrum (algebra A))) ∧
      (∃ h : @Homeomorph (PrimeSpectrum A)
          (closedPoints (PrimeSpectrum (algebra A)))
          (constructibleTopology (PrimeSpectrum A)) inferInstance,
        ∀ x : PrimeSpectrum A, (e (h x).val).val = (x, x)) ∧
      Module.FaithfullyFlat A (algebra A) ∧ IsWLocalRing (algebra A) := by
  classical
  have hdata := primeCharts A
  obtain ⟨e, he, hπ, hρ⟩ := hdata
  have hind : Algebra.IndZariski A (algebra A) := indZariski A
  have hlocal (q : PrimeSpectrum (algebra A)) :
      Nonempty (Localization.AtPrime q.asIdeal ≃ₐ[A]
        Localization.AtPrime (e q).val.2.asIdeal) := by
    let f : Localization.AtPrime (PrimeSpectrum.comap
        (algebraMap A (algebra A)) q).asIdeal →ₐ[A] Localization.AtPrime q.asIdeal :=
      { toRingHom := Localization.localRingHom _ _ (algebraMap A (algebra A)) rfl
        commutes' a := by
          change Localization.localRingHom _ _ (algebraMap A (algebra A)) rfl
              (algebraMap A _ a) =
            algebraMap (algebra A) _ (algebraMap A (algebra A) a)
          exact Localization.localRingHom_to_map .. }
    have hf : Function.Bijective f :=
      Algebra.BijectiveOnStalks.bijective_localRingHom q.asIdeal
    have hh := (AlgEquiv.ofBijective f hf).symm
    rw [he q] at hh
    exact ⟨hh⟩
  let δ (x : PrimeSpectrum A) : PrimeSpectrum (algebra A) :=
    e.symm ⟨(x, x), le_rfl⟩
  have hδ (x : PrimeSpectrum A) : (e (δ x)).val = (x, x) := by
    simp [δ]
  have hclopen (f : A) : IsClopen {q | f ∉ (e q).val.1.asIdeal} := by
    have h : @IsClopen (PrimeSpectrum A) (constructibleTopology (PrimeSpectrum A))
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) :=
      ⟨(PrimeSpectrum.isCompact_basicOpen f).isClosed_constructibleTopology_of_isOpen
          (PrimeSpectrum.basicOpen f).isOpen,
        (PrimeSpectrum.isCompact_basicOpen f).isOpen_constructibleTopology_of_isOpen
          (PrimeSpectrum.basicOpen f).isOpen⟩
    exact @IsClopen.preimage _ _ _ (constructibleTopology (PrimeSpectrum A))
      _ h (fun q ↦ (e q).val.1) hπ
  have hcc_first {q r : PrimeSpectrum (algebra A)} (hr : r ∈ connectedComponent q) :
      (e r).val.1 = (e q).val.1 := by
    apply PrimeSpectrum.ext
    ext f
    constructor
    · intro hfr
      by_contra hfq
      exact ((hclopen f).connectedComponent_subset hfq hr) hfr
    · intro hfq
      by_contra hfr
      exact ((hclopen f).compl.connectedComponent_subset (by simpa using hfq) hr) hfr
  have hspec_first {q r : PrimeSpectrum (algebra A)} (h : q ⤳ r) :
      (e r).val.1 = (e q).val.1 := by
    apply hcc_first
    have hh := ConnectedComponents.coe_eq_coe.mp h.connectedComponents_mk_eq
    rw [hh]
    exact mem_connectedComponent
  have hρδ (x : PrimeSpectrum A)
      (ρ : algebra A →ₐ[A] Localization.AtPrime x.asIdeal)
      (hrange : Set.range (PrimeSpectrum.comap ρ.toRingHom) = {q | (e q).val.1 = x}) :
      PrimeSpectrum.comap ρ.toRingHom (IsLocalRing.closedPoint _) = δ x := by
    apply e.injective
    apply Subtype.ext
    apply Prod.ext
    · exact (hrange ▸ Set.mem_range_self (IsLocalRing.closedPoint _)).trans
        (congrArg Prod.fst (hδ x)).symm
    · rw [← he, ← PrimeSpectrum.comap_comp_apply]
      have hcomp : ρ.toRingHom.comp (algebraMap A (algebra A)) =
          algebraMap A (Localization.AtPrime x.asIdeal) := by
        ext a
        exact ρ.commutes a
      rw [hcomp]
      apply PrimeSpectrum.ext
      change Ideal.comap _ (IsLocalRing.maximalIdeal _) = _
      rw [show Ideal.comap (algebraMap A (Localization.AtPrime x.asIdeal))
        (IsLocalRing.maximalIdeal _) = x.asIdeal from
          Localization.AtPrime.under_maximalIdeal]
      exact congrArg (fun z ↦ z.2.asIdeal) (hδ x).symm
  have hspecial (q : PrimeSpectrum (algebra A)) : q ⤳ δ (e q).val.1 := by
    obtain ⟨ρ, _, hrange⟩ := hρ (e q).val.1
    have hq : q ∈ Set.range (PrimeSpectrum.comap ρ.toRingHom) := by
      rw [hrange]
      rfl
    obtain ⟨p, hp⟩ := hq
    have hh := (IsLocalRing.specializes_closedPoint p).map (PrimeSpectrum.continuous_comap
      ρ.toRingHom)
    rw [hp, hρδ _ ρ hrange] at hh
    exact hh
  have hδclosed (x : PrimeSpectrum A) : IsClosed ({δ x} : Set _) := by
    obtain ⟨ρ, hclosed, hrange⟩ := hρ x
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ.toRingHom)) := hclosed
    have hc : Topology.IsClosedEmbedding (PrimeSpectrum.comap ρ.toRingHom) :=
      (Spec.map (CommRingCat.ofHom ρ.toRingHom)).isClosedEmbedding
    rw [← hρδ _ ρ hrange, ← Set.image_singleton]
    exact hc.isClosedMap _ (IsLocalRing.isClosed_singleton_closedPoint _)
  have hdiag (q : PrimeSpectrum (algebra A)) :
      q ∈ closedPoints (PrimeSpectrum (algebra A)) ↔ (e q).val.1 = (e q).val.2 := by
    constructor
    · intro hq
      have hh : δ (e q).val.1 = q :=
        Set.mem_singleton_iff.mp ((hspecial q).mem_closed
          (mem_closedPoints_iff.mp hq) (Set.mem_singleton q))
      have hp := hδ (e q).val.1
      rw [hh] at hp
      exact (congrArg Prod.fst hp).trans (congrArg Prod.snd hp).symm
    · intro hq
      have hh : q = δ (e q).val.1 := by
        apply e.injective
        apply Subtype.ext
        rw [hδ]
        exact Prod.ext rfl hq.symm
      rw [hh]
      exact mem_closedPoints_iff.mpr (hδclosed _)
  have hcomponents (q : PrimeSpectrum (algebra A)) :
      connectedComponent q = {r | (e r).val.1 = (e q).val.1} := by
    apply Set.Subset.antisymm (fun r hr ↦ hcc_first hr)
    intro r hr
    have hh : ConnectedComponents.mk r = ConnectedComponents.mk q := by
      rw [(hspecial r).connectedComponents_mk_eq, (hspecial q).connectedComponents_mk_eq, hr]
    have hh' := ConnectedComponents.coe_eq_coe.mp hh
    rw [← hh']
    exact mem_connectedComponent
  have hclosed : IsClosed (closedPoints (PrimeSpectrum (algebra A))) := by
    have hcompl : (closedPoints (PrimeSpectrum (algebra A)))ᶜ =
        ⋃ f : A, {q | f ∈ (e q).val.1.asIdeal} ∩
          (PrimeSpectrum.comap (algebraMap A (algebra A))) ⁻¹' PrimeSpectrum.basicOpen f := by
      ext q
      simp only [Set.mem_compl_iff, hdiag, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_preimage, he]
      constructor
      · intro hne
        have hlt : (e q).val.2.asIdeal < (e q).val.1.asIdeal :=
          lt_of_le_of_ne (e q).property (fun h ↦ hne (PrimeSpectrum.ext h.symm))
        exact SetLike.exists_of_lt hlt
      · rintro ⟨f, hf, hnf⟩ h
        exact hnf (h ▸ hf)
    rw [← isOpen_compl_iff, hcompl]
    refine isOpen_iUnion fun f ↦ ?_
    have hf : IsOpen {q | f ∈ (e q).val.1.asIdeal} := by
      simpa only [Set.compl_ofPred, not_not] using (hclopen f).compl.isOpen
    exact hf.inter
      ((PrimeSpectrum.basicOpen f).isOpen.preimage (PrimeSpectrum.continuous_comap _))
  have hw : IsWLocalRing (algebra A) := by
    refine ⟨{ toSpectralSpace := inferInstance
              isClosed_closedPoints := hclosed
              eq_of_specializes := ?_ }⟩
    intro q c c' hc hc' hqc hqc'
    have hcdiag := (hdiag c).mp (mem_closedPoints_iff.mpr hc)
    have hc'diag := (hdiag c').mp (mem_closedPoints_iff.mpr hc')
    have heq := (hspec_first hqc).trans (hspec_first hqc').symm
    apply e.injective
    apply Subtype.ext
    exact Prod.ext heq (hcdiag.symm.trans (heq.trans hc'diag))
  have hff : Module.FaithfullyFlat A (algebra A) := by
    apply Module.FaithfullyFlat.of_comap_surjective
    intro x
    refine ⟨δ x, ?_⟩
    rw [he]
    exact congrArg Prod.snd (hδ x)
  have hhomeo : ∃ h : @Homeomorph (PrimeSpectrum A)
      (closedPoints (PrimeSpectrum (algebra A)))
      (constructibleTopology (PrimeSpectrum A)) inferInstance,
      ∀ x : PrimeSpectrum A, (e (h x).val).val = (x, x) := by
    have : CompactSpace (closedPoints (PrimeSpectrum (algebra A))) :=
      isCompact_iff_compactSpace.mp hclosed.isCompact
    have : T2Space (WithConstructibleTopology (PrimeSpectrum A)) :=
      patchT2 A
    let g : closedPoints (PrimeSpectrum (algebra A)) ≃
        WithConstructibleTopology (PrimeSpectrum A) :=
      { toFun := fun q ↦ WithTopology.toTopology _ (e q.val).val.1
        invFun := fun x ↦ ⟨δ x.ofTopology, mem_closedPoints_iff.mpr (hδclosed _)⟩
        left_inv := fun q ↦ by
          apply Subtype.ext
          apply e.injective
          apply Subtype.ext
          rw [hδ]
          exact Prod.ext rfl ((hdiag q.val).mp q.property)
        right_inv := fun x ↦ by
          apply WithTopology.ofTopology_injective
          exact congrArg Prod.fst (hδ x.ofTopology) }
    have hg : Continuous g :=
      @Continuous.comp _ (PrimeSpectrum A) _ _
        (constructibleTopology (PrimeSpectrum A)) _ _ _
        (WithTopology.continuous_toTopology _)
        (@Continuous.comp _ (PrimeSpectrum (algebra A)) (PrimeSpectrum A) _ _
          (constructibleTopology (PrimeSpectrum A)) _ _ hπ continuous_subtype_val)
    let H := g.toHomeomorphOfContinuousClosed hg hg.isClosedMap
    let T : @Homeomorph (PrimeSpectrum A)
        (WithConstructibleTopology (PrimeSpectrum A))
        (constructibleTopology (PrimeSpectrum A)) inferInstance :=
      @Homeomorph.mk _ _ (constructibleTopology (PrimeSpectrum A)) _
        (WithTopology.equiv _ _).symm (WithTopology.continuous_toTopology _)
        (WithTopology.continuous_ofTopology _)
    refine ⟨@Homeomorph.trans _ _ _ (constructibleTopology (PrimeSpectrum A)) _ _ T H.symm, ?_⟩
    intro x
    exact hδ x
  exact ⟨e, he, hlocal, hπ, hcomponents, hρ, hdiag, hclosed, hhomeo, hff, hw⟩

end PrincipalWLocalization
end
