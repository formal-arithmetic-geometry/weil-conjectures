/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.Paper.EtaleCEStationaryPageNaturality
public import Sheaf.CategoryTheory.FilteredComplexQuotientCoherence
import WeilConjectures.CategoryTheory.CartanEilenbergAllLowerBounds
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCover
import Sheaf.Paper.EtaleCENormalizedRepresentativeCohomology
import Sheaf.Paper.EtaleCECanonicalRowComparison
import all Sheaf.Paper.EtaleCERowCyclesNaturality

/-! # Coherent quotient presentations and comparison of supplied first-page maps

Source: Stacks Project, Derived Categories, Tags 015J and 015K; Homology, Tag 012K.
(blueprint: lem-weil-pbc-ce-coherent-quotient-presentations).
-/

@[expose] public section


universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem rowInclusion_eq_rowι
    {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ)
    (h : (p : ℤ) + q = q + (p : ℤ)) :
    rowInclusion D p q (q + (p : ℤ)) h =
      Functor.secondFiltrationRowι
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) D.I p q := rfl

private theorem pageProjection_epi
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (pq : ℤ × ℤ) :
    Epi (filteredComplexPageπ K F r pq) := by
  unfold filteredComplexPageπ
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_coherence_of_normalized
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (E : CohomologicalSpectralSequence C 1)
    (δ : ∀ (r : ℤ) (_hr : 1 ≤ r), FilteredComplexPageDifferential K F r)
    (j : ∀ (r : ℤ) (hr : 1 ≤ r), E.page r hr ≅ (δ r hr).page)
    (hn : ∀ (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ),
      FilteredComplexHomologyNormalized K F r (δ r hr) pq
        ((HomologicalComplex.homologyFunctor C (ComplexShape.up' (r, 1 - r)) pq).mapIso
          (j r hr).symm ≪≫ E.iso r (r + 1) pq rfl hr ≪≫
          (HomologicalComplex.eval C (ComplexShape.up' (r + 1, 1 - (r + 1))) pq).mapIso
            (j (r + 1) (Int.le_add_one hr)))) :
    FilteredComplexQuotientCoherence K F E
      (fun p q r hr ↦ HomologicalComplex.Hom.isoApp (j r hr) (p, q)) := by
  constructor
  · intro r hr
    exact ⟨δ r hr, j r hr, fun _ _ ↦ rfl⟩
  · intro r hr p q hZ A x z hz
    obtain ⟨f, _, hf⟩ := filteredComplex_successor_cycles_cover K F r hr (δ r hr) (p, q) hZ
    have hzf : z = x ≫ f ≫ HomologicalComplex.cyclesMap (j r hr).inv (p, q) := by
      apply (cancel_mono ((E.page r hr).iCycles (p, q))).1
      change z ≫ (E.page r hr).iCycles (p, q) =
        x ≫ Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r (p, q) ≫
          (j r hr).inv.f (p, q) at hz
      simpa only [Category.assoc, HomologicalComplex.cyclesMap_i,
        HomologicalComplex.cyclesMap_i_assoc, hf, reassoc_of% hf] using hz
    have hnorm := hn r hr (p, q) hZ f hf
    change f ≫ (δ r hr).page.homologyπ (p, q) ≫
      HomologicalComplex.homologyMap (j r hr).inv (p, q) ≫
        (E.iso r (r + 1) (p, q) rfl hr).hom ≫ (j (r + 1) (Int.le_add_one hr)).hom.f (p, q) =
      filteredComplexPageπ K F (r + 1) (p, q) at hnorm
    change z ≫ (E.page r hr).homologyπ (p, q) ≫
      (E.iso r (r + 1) (p, q) rfl hr).hom ≫ (j (r + 1) (Int.le_add_one hr)).hom.f (p, q) = _
    rw [hzf]
    simpa only [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc] using
      congrArg (fun a ↦ x ≫ a) hnorm

-- Use the row-comparison equations without unfolding the chosen witnesses.
attribute [local irreducible] EtaleTermwiseHypercohomology.totalSectionsIso
  EtaleTermwiseHypercohomology.rowCycleStep EtaleTermwiseHypercohomology.rowCycleClass
  EtaleTermwiseHypercohomology.rowComparison EtaleTermwiseHypercohomology.firstPageIso
  ceRowSectionsMap ceSectionsLift rowInclusion Functor.secondFiltrationRowι
  filteredComplexPageπ filteredComplexPageObject
  cohomologyMap Sheaf.H.map Sheaf.H.mapFunctor

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in
-- Elaborate the simultaneous dependent CE families and summand equations together.
/-- Construct compatible pages and compute the first page of an already supplied map.
No spectral-sequence map, bicomplex comparison or total lift is constructed here.
Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-coherent-quotient-presentations).

Proof. Choose support-preserving augmented CE resolutions and apply the existing
normalized representative-cohomology construction to obtain all presentations,
concrete quotient pages and normalized successor comparisons simultaneously.
Evaluate the complex page isomorphisms in each bidegree to define e.
For successor coherence, use the successor-cycle cover of the concrete page.
Cancellation of the monic cycle inclusion identifies any representative in the
abstract page with the transported concrete cover. Homology-projection naturality
then turns its prescribed normalization equation into the required successor equation.
For the first-page equation use source sections-row cycles as the test object.
The canonical step and graded-cycle maps give its two representatives. In the
target precompose these maps with the cycles map of the sections row comparison.
Diagonal inclusion naturality supplies the filtered-representative relation; the
canonical cycle equations supply both graded projections. Apply the supplied
premise for m and the normalized ordinary-cohomology equation to this same pair.
Postcompose the former with the target first-page isomorphism and compare with
the latter. Cancel the source row-cycle isomorphism, epic boundary quotient and
inverse page isomorphism. No filtered-map premise or map on another component
is needed. Zero rows, zero complexes, p = 0 and empty schemes use the same
universal properties without extra assumptions. -/
theorem exists_etaleCE_coherent_quotient_presentations :
    ∃ (P : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (e : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleCEQuotientRealization (P X K)),
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        FilteredComplexQuotientCoherence (P X K).sectionsTotal (P X K).L
          (P X K).sequence (e X K)) ∧
      ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
      let D := P X K
      let D' := P Y L
      ∀ (φ : (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj D.I ⟶ D'.I)
    (hφ : ∀ q : ℤ,
      (upperStar AddCommGrpCat.{uNatural + 1} f).map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.obj.X q)).inv ≫
            (D.a.f q).f 0) ≫ (φ.f q).f 0 =
        v.f q ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.obj.X q)).inv ≫
            (D'.a.f q).f 0)
    (u : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.sheafTotal ⟶ D'.sheafTotal)
    (hu : ∀ (m : ℕ) (q n : ℤ) (h : (m : ℤ) + q = n),
        (upperStar AddCommGrpCat.{uNatural + 1} f).map
            ((HomologicalComplex.extendXIso
              (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ≫ u.f n =
          (φ.f q).f m ≫
            (HomologicalComplex.extendXIso
              (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D'.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h),
      let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
      ∀ (p : ℕ) (q : ℤ)
        (m : (D.sequence.page 1).X (q, (p : ℤ)) ⟶
          (D'.sequence.page 1).X (q, (p : ℤ))),
        (∀ (A : AddCommGrpCat.{uNatural + 1})
          (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
            (q + (p : ℤ)))
          (y : A ⟶ (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
            (q + (p : ℤ)))
          (z : A ⟶ (D.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1}))
          (z' : A ⟶ (D'.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1})),
          x ≫ (D.L.step q).arrow.f (q + (p : ℤ)) ≫ b.f (q + (p : ℤ)) =
            y ≫ (D'.L.step q).arrow.f (q + (p : ℤ)) →
          z ≫ (D.L.complexCycles q (q + (p : ℤ)) 1).arrow =
            x ≫ (D.L.complexQuotientπ q (q + 1) (Int.le_add_one (le_refl q))).f (q + (p : ℤ)) →
          z' ≫ (D'.L.complexCycles q (q + (p : ℤ)) 1).arrow =
            y ≫ (D'.L.complexQuotientπ q (q + 1) (Int.le_add_one (le_refl q))).f (q + (p : ℤ)) →
          z ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
              (e X K q (p : ℤ) 1 (by decide)).inv ≫ m =
            z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫
              (e Y L q (p : ℤ) 1 (by decide)).inv) →
        m ≫ (D'.firstPageIso p q).hom =
          (D.firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p)) := by
  classical
  have hraw (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})) :=
    exists_cartanEilenberg_resolution_all_lower_bounds
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) K
  choose I a hsupp hrows hterms hhorizontal hquasi using hraw
  have hbelow (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})) :
      ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero ((I X K).X s) := by
    obtain ⟨b, hb⟩ := K.property
    have : K.obj.IsStrictlyGE b := hb
    refine ⟨b, hsupp X K b (fun s hs ↦ K.obj.isZero_of_isStrictlyGE b s hs)⟩
  obtain ⟨P, δ, j, _, hn, hc⟩ := exists_etaleCE_normalized_representative_cohomology
    I a hbelow hrows hterms hhorizontal hquasi
  let e : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      EtaleCEQuotientRealization (P X K) :=
    fun X K q p r hr ↦ HomologicalComplex.Hom.isoApp (j X K r hr) (q, p)
  refine ⟨P, e, ?_, ?_⟩
  · intro X K
    exact quotient_coherence_of_normalized _ _ _ (δ X K) (j X K) (hn X K)
  · intro X Y f K L v D D' φ hφ u hu b p q m hm
    specialize hc f K L v φ hφ u hu
    let R := ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (D.I.X q)
    let t := HomologicalComplex.cyclesMap (ceRowSectionsMap f (φ.f q)) p
    have hι := rowInclusion_naturality f K L D D' φ u hu p q
      (q + (p : ℤ)) (add_comm _ _)
    rw [rowInclusion_eq_rowι, rowInclusion_eq_rowι] at hι
    have hxy : D.rowCycleStep p q ≫ (D.L.step q).arrow.f (q + (p : ℤ)) ≫
        b.f (q + (p : ℤ)) =
      (t ≫ D'.rowCycleStep p q) ≫ (D'.L.step q).arrow.f (q + (p : ℤ)) := by
      rw [← Category.assoc, D.rowCycleStep_arrow, Category.assoc, hι]
      simp only [Category.assoc, D'.rowCycleStep_arrow, t,
        HomologicalComplex.cyclesMap_i_assoc]
    have hz := D.rowCycleClass_arrow p q
    have hz' : (t ≫ D'.rowCycleClass p q) ≫
        (D'.L.complexCycles q (q + (p : ℤ)) 1).arrow =
      (t ≫ D'.rowCycleStep p q) ≫
        (D'.L.complexQuotientπ q (q + 1) (Int.le_add_one (le_refl q))).f
          (q + (p : ℤ)) := by
      simp only [Category.assoc, D'.rowCycleClass_arrow]
    have hmap :
        D.rowCycleClass p q ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
            (e X K q (p : ℤ) 1 (by decide)).inv ≫ m =
          (t ≫ D'.rowCycleClass p q) ≫
            filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫
              (e Y L q (p : ℤ) 1 (by decide)).inv :=
      hm (R.cycles p) (D.rowCycleStep p q) (t ≫ D'.rowCycleStep p q)
        (D.rowCycleClass p q) (t ≫ D'.rowCycleClass p q) hxy hz hz'
    have hcoh :
        D.rowCycleClass p q ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
            (e X K q (p : ℤ) 1 (by decide)).inv ≫ (D.firstPageIso p q).hom ≫
              AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
                (cohomologyMap f (K.obj.X q) p)) =
          (t ≫ D'.rowCycleClass p q) ≫
            filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫
              (e Y L q (p : ℤ) 1 (by decide)).inv ≫ (D'.firstPageIso p q).hom := by
      exact hc (R.cycles p) p q
        (D.rowCycleStep p q) (t ≫ D'.rowCycleStep p q)
        (D.rowCycleClass p q) (t ≫ D'.rowCycleClass p q) hxy hz hz'
    have : IsIso (D.rowCycleClass p q) := D.rowCycleClass_isIso p q
    have : Epi (filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ))) :=
      pageProjection_epi D.sectionsTotal D.L 1 (q, (p : ℤ))
    apply (cancel_epi (D.rowCycleClass p q ≫
      filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
        (e X K q (p : ℤ) 1 (by decide)).inv)).1
    calc
      _ = (t ≫ D'.rowCycleClass p q) ≫
          filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫
            (e Y L q (p : ℤ) 1 (by decide)).inv ≫ (D'.firstPageIso p q).hom := by
        simpa only [Category.assoc] using
          congrArg (fun a ↦ a ≫ (D'.firstPageIso p q).hom) hmap
      _ = _ := by
        simpa only [Category.assoc] using hcoh.symm

end AlgebraicGeometry.Etale
