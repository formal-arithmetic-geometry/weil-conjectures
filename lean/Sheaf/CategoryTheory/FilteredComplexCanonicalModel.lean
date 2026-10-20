/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.CategoryTheory.FilteredComplexCanonicalSequence
public import Sheaf.CategoryTheory.FilteredPageTwoModel
import Sheaf.Algebra.Homology.FilteredComplexQuotientImageComparison
import Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis
import all WeilConjectures.CategoryTheory.FilteredQuotientPageMaps
import all Sheaf.CategoryTheory.FilteredQuotientComparisons
import all Sheaf.CategoryTheory.FilteredQuotientMapRestrictions

/-! # A concrete functorial filtered page-two model

Source: Stacks Project, Tag 012K, the cycle and boundary quotient and its image description.
(blueprint: lem-sp-filtered-complex-canonical-model).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The interval inclusion kills the smaller filtration step.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-model). -/
theorem filteredComplexCanonicalQuotientMap_zero
    (U : FilteredObject (CochainComplex C ℤ)) (p r : ℤ) (hr : 2 ≤ r) :
    Subobject.ofLE (U.filtration.step (p + r)) (U.filtration.step p)
        (U.filtration.antitone_step (by omega)) ≫
      (Subobject.ofLE (U.filtration.step p) (U.filtration.step (p - r + 1))
        (U.filtration.antitone_step (by omega)) ≫
        U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)) = 0 := by
  rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
  rw [← Subobject.ofLE_comp_ofLE (U.filtration.step (p + r))
    (U.filtration.step (p + 1)) (U.filtration.step (p - r + 1))
    (U.filtration.antitone_step (by omega)) (U.filtration.antitone_step (by omega))]
  simp only [Category.assoc, DecreasingFiltration.complexQuotientπ,
    cokernel.condition, comp_zero]

/-- The actual map of interval quotient complexes.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-model). -/
noncomputable def filteredComplexCanonicalQuotientMap
    (U : FilteredObject (CochainComplex C ℤ)) (p r : ℤ) (hr : 2 ≤ r) :
    U.filtration.complexQuotient p (p + r) (by omega) ⟶
      U.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) :=
  cokernel.desc _
    (Subobject.ofLE (U.filtration.step p) (U.filtration.step (p - r + 1))
      (U.filtration.antitone_step (by omega)) ≫
      U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega))
    (filteredComplexCanonicalQuotientMap_zero U p r hr)

/-- The quotient projection equation.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-model). -/
theorem filteredComplexCanonicalQuotientMap_comm
    (U : FilteredObject (CochainComplex C ℤ)) (p r : ℤ) (hr : 2 ≤ r) :
    U.filtration.complexQuotientπ p (p + r) (by omega) ≫
        filteredComplexCanonicalQuotientMap U p r hr =
      Subobject.ofLE (U.filtration.step p) (U.filtration.step (p - r + 1))
        (U.filtration.antitone_step (by omega)) ≫
        U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) :=
  cokernel.π_desc _ _ _

/-- The representative equation that specifies the image comparison uniquely.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-model). -/
def FilteredComplexCanonicalImageIsoProperty
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (e : filteredComplexPageObject U.obj U.filtration r (p, q) ≅
      image (HomologicalComplex.homologyMap (filteredComplexCanonicalQuotientMap U p r hr)
        (p + q))) : Prop :=
  ∀ (z : (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
        (U.filtration.complexCycles p (p + q) r : C))
    (g : (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
      (U.filtration.complexQuotient p (p + r) (by omega)).cycles (p + q)),
    z ≫ (U.filtration.complexCycles p (p + q) r).arrow =
      (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
        (U.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) →
    g ≫ (U.filtration.complexQuotient p (p + r) (by omega)).iCycles (p + q) =
      (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
        (U.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) →
    z ≫ filteredComplexPageπ U.obj U.filtration r (p, q) ≫ e.hom ≫
        image.ι (HomologicalComplex.homologyMap (filteredComplexCanonicalQuotientMap U p r hr)
          (p + q)) =
      g ≫ (U.filtration.complexQuotient p (p + r) (by omega)).homologyπ (p + q) ≫
        HomologicalComplex.homologyMap (filteredComplexCanonicalQuotientMap U p r hr) (p + q)

/-- The quotient-image comparison is the uniquely specified representative map.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-model).

Proof. The quotient-image theorem gives the comparison on representatives. The interval
map is unique after its epic projection, hence equals the actual cokernel map above.
The representative maps are unique after their monic cycle inclusions. Finally the
representatives cover the graded cycles and the boundary quotient is epic, so their
composite determines the comparison uniquely. -/
theorem filteredComplexCanonicalImageIso_exists_unique
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    ∃! e : filteredComplexPageObject U.obj U.filtration r (p, q) ≅
        image (HomologicalComplex.homologyMap (filteredComplexCanonicalQuotientMap U p r hr)
          (p + q)), FilteredComplexCanonicalImageIsoProperty U p q r hr e := by
  obtain ⟨ha, hb, φ, hφ, z, g, hz, hg, e, he⟩ :=
    U.filtration.filteredComplex_quotient_image_comparison p (p + q) r (by omega)
      (filteredComplex_boundaries_le_cycles U.obj U.filtration p (p + q) r)
  have : Epi (U.filtration.complexQuotientπ p (p + r) (by omega)) := by
    unfold DecreasingFiltration.complexQuotientπ
    infer_instance
  have hφeq : φ = filteredComplexCanonicalQuotientMap U p r hr := by
    apply (cancel_epi (U.filtration.complexQuotientπ p (p + r)
      ((Int.le_add_one le_rfl).trans hb))).1
    exact hφ.trans (filteredComplexCanonicalQuotientMap_comm U p r hr).symm
  subst φ
  have hn : FilteredComplexCanonicalImageIsoProperty U p q r hr e := by
    intro z' g' hz' hg'
    have hzz : z' = z := (cancel_mono _).1 (hz'.trans hz.symm)
    have hgg : g' = g := (cancel_mono _).1 (hg'.trans hg.symm)
    simpa only [hzz, hgg, filteredComplexPageπ] using he
  refine ⟨e, hn, ?_⟩
  intro e' he'
  obtain ⟨z', g', hze, _, hz', hg'⟩ :=
    U.filtration.filteredComplex_representative_epis p (p + q) r (by omega)
  have : Epi z' := hze
  have : Epi (filteredComplexPageπ U.obj U.filtration r (p, q)) := by
    unfold filteredComplexPageπ
    infer_instance
  apply Iso.ext
  apply (cancel_mono (image.ι (HomologicalComplex.homologyMap
    (filteredComplexCanonicalQuotientMap U p r hr) (p + q)))).1
  apply (cancel_epi (z' ≫ filteredComplexPageπ U.obj U.filtration r (p, q))).1
  simpa only [Category.assoc] using
    (he' z' g' hz' hg').trans (hn z' g' hz' hg').symm

/-- The normalized image comparison for the concrete quotient pages.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-model). -/
noncomputable def filteredComplexCanonicalImageIso
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    filteredComplexPageObject U.obj U.filtration r (p, q) ≅
      image (HomologicalComplex.homologyMap (filteredComplexCanonicalQuotientMap U p r hr)
        (p + q)) :=
  (filteredComplexCanonicalImageIso_exists_unique U p q r hr).choose

/-- The constructed image comparison has its defining normalization.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-model). -/
theorem filteredComplexCanonicalImageIso_property
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    FilteredComplexCanonicalImageIsoProperty U p q r hr
      (filteredComplexCanonicalImageIso U p q r hr) :=
  (filteredComplexCanonicalImageIso_exists_unique U p q r hr).choose_spec.1

private theorem representative_differential_lift
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K) (p n r n' : ℤ) (hn : n' = n + 1) :
    let R := F.complexCycleRepresentatives p n r
    let R' := F.complexCycleRepresentatives (p + r) n' r
    ∃ (y : (R : C) ⟶ (F.step (p + r) : CochainComplex C ℤ).X n')
      (v : (R : C) ⟶ (R' : C)),
      y ≫ (F.step (p + r)).arrow.f n' =
        R.arrow ≫ (F.step p).arrow.f n ≫ K.d n n' ∧ v ≫ R'.arrow = y := by
  subst n'
  let R := F.complexCycleRepresentatives p n r
  let R' := F.complexCycleRepresentatives (p + r) (n + 1) r
  have htr : (F.complexStep p n ⊓
      (Subobject.pullback (K.d n (n + 1))).obj (F.complexStep (p + r) (n + 1))).Factors
      (R.arrow ≫ (F.step p).arrow.f n) :=
    (pullback_factors_iff _ _ _).mp R.factors_self
  have hdt : (F.complexStep (p + r) (n + 1)).Factors
      (R.arrow ≫ (F.step p).arrow.f n ≫ K.d n (n + 1)) := by
    have hh := (pullback_factors_iff _ _ _).mp
      (Subobject.factors_right_of_inf_factors htr)
    simpa only [Category.assoc] using hh
  rw [DecreasingFiltration.complexStep, imageSubobject_mono] at hdt
  obtain ⟨y, hy⟩ : ∃ y : (R : C) ⟶ (F.step (p + r) : CochainComplex C ℤ).X (n + 1),
      y ≫ (F.step (p + r)).arrow.f (n + 1) =
        R.arrow ≫ (F.step p).arrow.f n ≫ K.d n (n + 1) :=
    (Subobject.mk_factors_iff _ _).mp hdt
  have hf : R'.Factors y := by
    apply (pullback_factors_iff _ _ _).mpr
    apply (Subobject.inf_factors _).mpr
    constructor
    · exact imageSubobject_factors_comp_self _ _
    · apply (pullback_factors_iff _ _ _).mpr
      rw [hy]
      simp only [Category.assoc, K.d_comp_d, comp_zero]
      exact Subobject.factors_zero
  exact ⟨y, R'.factorThru y hf, hy, Subobject.factorThru_arrow _ _ _⟩

/-- The image-model differential is represented by the original complex differential.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-model).

Proof. Lift the differential of an unquotiented cycle to the (p+r)-th step. Its next
differential is zero, so this lift factors through the target representative object.
Apply the defining representative equation of the concrete page differential and
the two normalized image comparisons. Naturality of the cycle and homology maps
identifies the resulting quotient maps with the displayed target cycle map. -/
theorem filteredComplexCanonicalModel_differential
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    let R := U.filtration.complexCycleRepresentatives p (p + q) r
    let Q := U.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)
    let Q' := U.filtration.complexQuotient (p + r - r + 1) (p + r + 1) (by omega)
    let n' := p + r + (q + 1 - r)
    ∃ (g : (R : C) ⟶ Q.cycles (p + q))
      (z : (R : C) ⟶ image (HomologicalComplex.homologyMap
        (filteredComplexCanonicalQuotientMap U p r hr) (p + q)))
      (y : (R : C) ⟶ (U.filtration.step (p + r) : CochainComplex C ℤ).X n')
      (h : (R : C) ⟶ Q'.cycles n'),
      g ≫ Q.iCycles (p + q) = R.arrow ≫
        (Subobject.ofLE (U.filtration.step p) (U.filtration.step (p - r + 1))
          (U.filtration.antitone_step (by omega))).f (p + q) ≫
        (U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)).f (p + q) ∧
      z ≫ image.ι (HomologicalComplex.homologyMap
          (filteredComplexCanonicalQuotientMap U p r hr) (p + q)) =
        g ≫ Q.homologyπ (p + q) ∧
      y ≫ (U.filtration.step (p + r)).arrow.f n' =
        R.arrow ≫ (U.filtration.step p).arrow.f (p + q) ≫ U.obj.d (p + q) n' ∧
      h ≫ Q'.iCycles n' = y ≫
        (Subobject.ofLE (U.filtration.step (p + r))
          (U.filtration.step (p + r - r + 1))
          (U.filtration.antitone_step (by omega))).f n' ≫
        (U.filtration.complexQuotientπ (p + r - r + 1) (p + r + 1) (by omega)).f n' ∧
      z ≫ (filteredComplexCanonicalImageIso U p q r hr).inv ≫
        ((filteredComplexCanonicalPageTwoFunctor.obj U).page r hr).d
          (p, q) (p + r, q + 1 - r) ≫
        (filteredComplexCanonicalImageIso U (p + r) (q + 1 - r) r hr).hom ≫
        image.ι (HomologicalComplex.homologyMap
          (filteredComplexCanonicalQuotientMap U (p + r) r hr) n') =
        h ≫ Q'.homologyπ n' := by
  dsimp only
  let F := U.filtration
  let R := F.complexCycleRepresentatives p (p + q) r
  let n' := p + r + (q + 1 - r)
  let R' := F.complexCycleRepresentatives (p + r) n' r
  let φ := filteredComplexCanonicalQuotientMap U p r hr
  let φ' := filteredComplexCanonicalQuotientMap U (p + r) r hr
  obtain ⟨z₀, g₀, _, _, hz₀, hg₀⟩ :=
    F.filteredComplex_representative_epis p (p + q) r (by omega)
  obtain ⟨z₁, g₁, _, _, hz₁, hg₁⟩ :=
    F.filteredComplex_representative_epis (p + r) n' r (by omega)
  obtain ⟨y, v, hy, hv⟩ := representative_differential_lift F p (p + q) r n' (by dsimp [n']; omega)
  let g := g₀ ≫ HomologicalComplex.cyclesMap φ (p + q)
  let z := z₀ ≫ filteredComplexPageπ U.obj F r (p, q) ≫
    (filteredComplexCanonicalImageIso U p q r hr).hom
  let h := v ≫ g₁ ≫ HomologicalComplex.cyclesMap φ' n'
  have hφ := congrArg (fun a ↦ a.f (p + q))
    (filteredComplexCanonicalQuotientMap_comm U p r hr)
  have hφ' := congrArg (fun a ↦ a.f n')
    (filteredComplexCanonicalQuotientMap_comm U (p + r) r hr)
  simp only [HomologicalComplex.comp_f] at hφ hφ'
  have hz := filteredComplexCanonicalImageIso_property U p q r hr z₀ g₀ hz₀ hg₀
  have hz' := filteredComplexCanonicalImageIso_property U (p + r) (q + 1 - r) r hr
    z₁ g₁ hz₁ hg₁
  refine ⟨g, z, y, h, ?_, ?_, hy, ?_, ?_⟩
  · simp only [g, Category.assoc, HomologicalComplex.cyclesMap_i]
    rw [← Category.assoc, hg₀, Category.assoc, hφ]
  · have hn := congrArg (fun a ↦ g₀ ≫ a)
      (HomologicalComplex.homologyπ_naturality φ (p + q))
    simpa only [g, z, φ, F, Category.assoc] using hz.trans hn
  · change (v ≫ g₁ ≫ HomologicalComplex.cyclesMap φ' n') ≫ _ = _
    rw [Category.assoc, Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc g₁, hg₁, Category.assoc, hφ']
    simp only [← Category.assoc, hv]
    rfl
  · have hyz : (v ≫ z₁) ≫ (F.complexCycles (p + r) n' r).arrow =
        y ≫ (F.complexQuotientπ (p + r) (p + r + 1) (by omega)).f n' := by
      rw [Category.assoc, hz₁, ← Category.assoc, hv]
    have hd := (filteredComplexCanonicalDifferential U r (by omega)).on_representatives
      (R : C) (p, q) (p + r, q + 1 - r) (by ext <;> simp [sub_eq_add_neg, add_assoc])
      R.arrow y z₀ (v ≫ z₁) hy.symm hz₀ hyz
    dsimp only [filteredComplexCanonicalPageTwoFunctor, filteredComplexCanonicalSequence]
    simp only [z, Category.assoc, Iso.hom_inv_id_assoc]
    change z₀ ≫ filteredComplexPageπ U.obj F r (p, q) ≫
      (filteredComplexCanonicalDifferential U r (by omega)).d (p, q) (p + r, q + 1 - r) ≫
      (filteredComplexCanonicalImageIso U (p + r) (q + 1 - r) r hr).hom ≫ _ = _
    calc
      _ = (v ≫ z₁) ≫ filteredComplexPageπ U.obj F r (p + r, q + 1 - r) ≫
          (filteredComplexCanonicalImageIso U (p + r) (q + 1 - r) r hr).hom ≫
          image.ι (HomologicalComplex.homologyMap φ' n') := by
        simpa only [Category.assoc] using congrArg
          (fun a ↦ a ≫ (filteredComplexCanonicalImageIso U (p + r) (q + 1 - r) r hr).hom ≫
            image.ι (HomologicalComplex.homologyMap φ' n')) hd
      _ = _ := by
        have hn := congrArg (fun a ↦ g₁ ≫ a)
          (HomologicalComplex.homologyπ_naturality φ' n')
        simpa only [h, Category.assoc] using
          congrArg (fun a ↦ v ≫ a) (hz'.trans hn)

private theorem representative_map
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V)
    (s : ∀ a : ℤ, (U.filtration.step a : CochainComplex C ℤ) ⟶
      (V.filtration.step a : CochainComplex C ℤ))
    (hs : ∀ a, s a ≫ (V.filtration.step a).arrow = (U.filtration.step a).arrow ≫ t.hom)
    (p n r : ℤ) :
    ∃ ρ : (U.filtration.complexCycleRepresentatives p n r : C) ⟶
        (V.filtration.complexCycleRepresentatives p n r : C),
      ρ ≫ (V.filtration.complexCycleRepresentatives p n r).arrow =
        (U.filtration.complexCycleRepresentatives p n r).arrow ≫ (s p).f n := by
  have hstep := preserves_steps U.obj V.obj U.filtration V.filtration t.hom s hs
  apply restriction
  unfold DecreasingFiltration.complexCycleRepresentatives
  apply preserves_pullback _ _ _ _ (congrArg (fun h ↦ h.f n) (hs p)).symm
  apply preserves_inf
  · exact hstep p n
  · exact preserves_pullback (t.hom.f n) (t.hom.f (n + 1))
      (U.obj.d n (n + 1)) (V.obj.d n (n + 1)) (t.hom.comm n (n + 1)).symm _ _
      (hstep (p + r) (n + 1))

/-- The normalized quotient-image comparison is natural in filtered maps.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-model).

Proof. Restrict the map to all steps and descend it to both interval quotient
complexes. Their defining projection equations imply the square with the interval
map. The chain map preserves the representative pullbacks; the induced map commutes
with the graded-cycle maps and the quotient-cycle maps after their monic inclusions.
The canonical page map is its boundary quotient. Apply the normalized image
naturality equation, proved by cancellation of the epic representative projection. -/
theorem filteredComplexCanonicalModel_naturality
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V)
    (p q r : ℤ) (hr : 2 ≤ r) :
    ∃ (s : ∀ a : ℤ, (U.filtration.step a : CochainComplex C ℤ) ⟶
        (V.filtration.step a : CochainComplex C ℤ))
      (a : U.filtration.complexQuotient p (p + r) (by omega) ⟶
        V.filtration.complexQuotient p (p + r) (by omega))
      (b : U.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) ⟶
        V.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)),
      (∀ i, s i ≫ (V.filtration.step i).arrow = (U.filtration.step i).arrow ≫ t.hom) ∧
      U.filtration.complexQuotientπ p (p + r) (by omega) ≫ a =
        s p ≫ V.filtration.complexQuotientπ p (p + r) (by omega) ∧
      U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ≫ b =
        s (p - r + 1) ≫ V.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ∧
      HomologicalComplex.homologyMap (filteredComplexCanonicalQuotientMap U p r hr) (p + q) ≫
          HomologicalComplex.homologyMap b (p + q) =
        HomologicalComplex.homologyMap a (p + q) ≫
          HomologicalComplex.homologyMap (filteredComplexCanonicalQuotientMap V p r hr) (p + q) ∧
      ((filteredComplexCanonicalPageTwoFunctor.map t).hom r hr).f (p, q) ≫
          (filteredComplexCanonicalImageIso V p q r hr).hom ≫
          image.ι (HomologicalComplex.homologyMap
            (filteredComplexCanonicalQuotientMap V p r hr) (p + q)) =
        (filteredComplexCanonicalImageIso U p q r hr).hom ≫
          image.ι (HomologicalComplex.homologyMap
            (filteredComplexCanonicalQuotientMap U p r hr) (p + q)) ≫
            HomologicalComplex.homologyMap b (p + q) := by
  let S := quotientPageSquares t r
  obtain ⟨a, ha⟩ := quotient_descent U.filtration V.filtration t.hom S.s S.hs p (p + r)
    (by omega)
  obtain ⟨b, hb⟩ := quotient_descent U.filtration V.filtration t.hom S.s S.hs
    (p - r + 1) (p + 1) (by omega)
  have hw : a ≫ filteredComplexCanonicalQuotientMap V p r hr =
      filteredComplexCanonicalQuotientMap U p r hr ≫ b := by
    have : Epi (U.filtration.complexQuotientπ p (p + r) (by omega)) := by
      unfold DecreasingFiltration.complexQuotientπ
      infer_instance
    apply (cancel_epi (U.filtration.complexQuotientπ p (p + r)
      (show p ≤ p + r by omega))).1
    rw [← Category.assoc, ha, Category.assoc, filteredComplexCanonicalQuotientMap_comm]
    rw [← Category.assoc, ← step_restriction_square U.filtration V.filtration
      t.hom S.s S.hs (p - r + 1) p (by omega)]
    rw [Category.assoc, ← hb, ← Category.assoc, ← filteredComplexCanonicalQuotientMap_comm,
      Category.assoc]
  refine ⟨S.s, a, b, S.hs, ha, hb, ?_, ?_⟩
  · simp only [← HomologicalComplex.homologyMap_comp, hw]
  · obtain ⟨ρ, hρ⟩ := representative_map t S.s S.hs p (p + q) r
    obtain ⟨zU, gU, hzUepi, _, hzU, hgU⟩ :=
      U.filtration.filteredComplex_representative_epis p (p + q) r (by omega)
    obtain ⟨zV, gV, _, _, hzV, hgV⟩ :=
      V.filtration.filteredComplex_representative_epis p (p + q) r (by omega)
    have : Epi zU := hzUepi
    have : Epi (filteredComplexPageπ U.obj U.filtration r (p, q)) := by
      unfold filteredComplexPageπ
      infer_instance
    have heU := filteredComplexCanonicalImageIso_property U p q r hr zU gU hzU hgU
    have heV := filteredComplexCanonicalImageIso_property V p q r hr zV gV hzV hgV
    have hg_n := congrArg (fun f ↦ f.f (p + q)) (S.hg p)
    have ha_n := congrArg (fun f ↦ f.f (p + q)) ha
    have hzρ : zU ≫ S.kz (p, q) = ρ ≫ zV := by
      apply (cancel_mono (V.filtration.complexCycles p (p + q) r).arrow).1
      rw [Category.assoc, S.hkz, ← Category.assoc, hzU, Category.assoc]
      rw [show (U.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ≫
          (S.g p).f (p + q) = (S.s p).f (p + q) ≫
            (V.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) from hg_n]
      rw [← Category.assoc, ← hρ, Category.assoc, ← hzV, ← Category.assoc]
    have hgρ : gU ≫ HomologicalComplex.cyclesMap a (p + q) = ρ ≫ gV := by
      apply (cancel_mono ((V.filtration.complexQuotient p (p + r)
        (show p ≤ p + r by omega)).iCycles (p + q))).1
      rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, hgU,
        Category.assoc]
      rw [show (U.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) ≫
          a.f (p + q) = (S.s p).f (p + q) ≫
            (V.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) from ha_n]
      rw [← Category.assoc, ← hρ, Category.assoc, ← hgV, ← Category.assoc]
    have hmap := filteredComplexCanonicalMap_property t p q r (by omega)
      S.s (S.g p) (S.kz (p, q)) (S.k (p, q)) S.hs (S.hg p) (S.hkz (p, q)) (S.hk (p, q))
    change ((filteredComplexCanonicalMap t).hom r _).f (p, q) ≫ _ = _
    rw [hmap]
    exact normalized_image_naturality (p + q) a b
      (filteredComplexCanonicalQuotientMap U p r hr)
      (filteredComplexCanonicalQuotientMap V p r hr) hw ρ zU zV gU gV
      (filteredComplexPageπ U.obj U.filtration r (p, q))
      (filteredComplexPageπ V.obj V.filtration r (p, q))
      (filteredComplexCanonicalImageIso U p q r hr).hom
      (filteredComplexCanonicalImageIso V p q r hr).hom heU heV
      (S.kz (p, q)) (S.k (p, q)) hzρ hgρ (S.hk (p, q))

/-- The concrete model, with normalized successor isomorphisms and quotient-image maps.
Source: Stacks, Tag 012K (blueprint: lem-sp-filtered-complex-canonical-model). -/
noncomputable def filteredComplexCanonicalModel (C : Type u) [Category.{v} C] [Abelian C] :
    FilteredPageTwoModel C where
  S := filteredComplexCanonicalPageTwoFunctor
  φ := filteredComplexCanonicalQuotientMap
  comm_φ := filteredComplexCanonicalQuotientMap_comm
  pageIso := filteredComplexCanonicalImageIso
  differential := filteredComplexCanonicalModel_differential
  naturality := filteredComplexCanonicalModel_naturality

end CategoryTheory
