/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.CategoryTheory.BoundedFilteredComplexPageCore
public import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology
import all Sheaf.CategoryTheory.BoundedFilteredComplexPageCore
import all Sheaf.CategoryTheory.FilteredQuotientComparisons
import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredQuotientPageMaps
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCover
import Sheaf.CategoryTheory.FilteredQuotientHomologyNaturality
import Sheaf.CategoryTheory.FilteredQuotientMapRestrictions
import Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure
import Sheaf.CategoryTheory.BoundedFilteredCoupleAbutment

/-!
# Finite filtered page functor with normalized successor maps

Source: Stacks Project, Homology, Tags 012K, 012M and 012O, cycle/boundary formulas,
filtered-complex spectral sequence and functoriality.
(blueprint: lem-kun-filtered-page-functor-normalized).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

-- Retain the representative equation in the proof of filteredQuotient_comparisons_rest.
-- Its private helpers specify the same maps by monic inclusion and epic projection squares.
private theorem normalizedPage_comparisons
    (C : Type u) [Category.{v} C] [Abelian C]
    (φ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
        U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
    (hφ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ φ U p r hr =
          Subobject.ofLE (U.obj.filtration.step p)
            (U.obj.filtration.step (p - r + 1))
            (U.obj.filtration.antitone_step (by omega)) ≫
              U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega))
    (hBZ :  ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (_hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r) :
    ∃ eH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q),
    ∃ (eQ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
        (p q r : ℤ) (hr : 1 ≤ r),
      cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)) ≅
        image (HomologicalComplex.homologyMap (φ U p r hr) (p + q))),
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (hr : 1 ≤ r),
      ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
          (U.obj.filtration.complexCycles p (p + q) r : C))
        (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
          (U.obj.filtration.complexQuotient p (p + r) (by omega)).cycles (p + q)),
        z ≫ (U.obj.filtration.complexCycles p (p + q) r).arrow =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        g ≫ (U.obj.filtration.complexQuotient p (p + r) (by omega)).iCycles (p + q) =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫ (eQ U p q r hr).hom ≫
            image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) =
          g ≫ (U.obj.filtration.complexQuotient p (p + r) (by omega)).homologyπ (p + q) ≫
            HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ∧
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.complexCycles p (p + q) 1 : C))
        (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.gradedPiece p).cycles (p + q)),
        z ≫ (U.obj.filtration.complexCycles p (p + q) 1).arrow =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        g ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
            (eH U p q).hom =
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q)) ∧
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        (eQ U p q 1 (by omega)).hom ≫
            image.ι (HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) =
          (eH U p q).hom ≫
            HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) ∧
      (∀ (U V : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (t : U ⟶ V) (p q r : ℤ) (hr : 1 ≤ r),
        ∃ (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex C ℤ) ⟶
            (V.obj.filtration.step a : CochainComplex C ℤ))
          (a : U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
            V.obj.filtration.complexQuotient p (p + r) (by omega))
          (b : U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) ⟶
            V.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
          (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p)
          (kz : (U.obj.filtration.complexCycles p (p + q) r : C) ⟶
            (V.obj.filtration.complexCycles p (p + q) r : C))
          (k : cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)) ⟶
            cokernel (Subobject.ofLE _ _ (hBZ V p q r hr))),
          (∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
            (U.obj.filtration.step i).arrow ≫ t.hom.hom) ∧
          U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ a =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + r) (by omega) ∧
          U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ≫ b =
            s (p - r + 1) ≫
              V.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ∧
          U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
          kz ≫ (V.obj.filtration.complexCycles p (p + q) r).arrow =
            (U.obj.filtration.complexCycles p (p + q) r).arrow ≫ g.f (p + q) ∧
          cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫ k =
            kz ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q r hr)) ∧
          (∃ (kz₁ : (U.obj.filtration.complexCycles p (p + q) 1 : C) ⟶
              (V.obj.filtration.complexCycles p (p + q) 1 : C))
            (k₁ : cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ⟶
              cokernel (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))),
            kz₁ ≫ (V.obj.filtration.complexCycles p (p + q) 1).arrow =
              (U.obj.filtration.complexCycles p (p + q) 1).arrow ≫ g.f (p + q) ∧
            cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫ k₁ =
              kz₁ ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))) ∧
          (∀ k₁ : cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ⟶
              cokernel (Subobject.ofLE _ _ (hBZ V p q 1 (by omega))),
            (∃ kz₁ : (U.obj.filtration.complexCycles p (p + q) 1 : C) ⟶
                (V.obj.filtration.complexCycles p (p + q) 1 : C),
              kz₁ ≫ (V.obj.filtration.complexCycles p (p + q) 1).arrow =
                (U.obj.filtration.complexCycles p (p + q) 1).arrow ≫ g.f (p + q) ∧
              cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫ k₁ =
                kz₁ ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))) →
            k₁ ≫ (eH V p q).hom =
              (eH U p q).hom ≫ HomologicalComplex.homologyMap g (p + q)) ∧
          k ≫ (eQ V p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ V p r hr) (p + q)) =
            (eQ U p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ≫
                HomologicalComplex.homologyMap b (p + q)) := by
  classical
  have hH₀ := fun (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ) ↦
    first_page_comparison U.obj.filtration p (p + q)
    (hBZ U p q 1 (by omega))
  choose eH hH using hH₀
  have hQ₀ := fun (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r) ↦ comparison_on_representatives U.obj.filtration p (p + q)
    r hr (hBZ U p q r hr) (φ U p r hr) (hφ U p r hr)
  choose eQ hQ using hQ₀
  refine ⟨eH, eQ, hQ, hH, ?_, ?_⟩
  · intro U p q
    obtain ⟨z, g, hz, hg, hz_epi, heH⟩ := hH U p q
    obtain ⟨z', g', hz', hg', _, heQ⟩ := hQ U p q 1 (by omega)
    have hzz : z' = z :=
      (cancel_mono (U.obj.filtration.complexCycles p (p + q) 1).arrow).1
        (hz'.trans hz.symm)
    have hgg : g' = g :=
      (cancel_mono ((U.obj.filtration.gradedPiece p).iCycles (p + q))).1
        (hg'.trans hg.symm)
    subst z'
    subst g'
    have := hz_epi
    apply (cancel_epi (cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))))).1
    apply (cancel_epi z).1
    have heH' := congrArg (fun f ↦
      f ≫ HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) heH
    exact heQ.trans (by
      simpa only [Category.assoc, DecreasingFiltration.gradedPiece,
        DecreasingFiltration.gr,
        DecreasingFiltration.complexQuotient] using heH'.symm)
  · intro U V t p q r hr
    choose s hs using t.hom.preserves
    obtain ⟨a, ha⟩ := quotient_descent U.obj.filtration V.obj.filtration t.hom.hom
      s hs p (p + r) (by omega)
    obtain ⟨b, hb⟩ := quotient_descent U.obj.filtration V.obj.filtration t.hom.hom
      s hs (p - r + 1) (p + 1) (by omega)
    obtain ⟨g, hg⟩ := quotient_descent U.obj.filtration V.obj.filtration t.hom.hom
      s hs p (p + 1) (by omega)
    obtain ⟨kz, k, hkz, hk, hk₁, ρ, hρ⟩ :=
      filteredQuotient_map_restrictions C hBZ U V t p q r hr
        s g hs hg
    refine ⟨s, a, b, g, kz, k, hs, ha, hb, hg, hkz, hk, hk₁, ?_, ?_⟩
    · intro k₁ h₁
      obtain ⟨kz₁, hkz₁, hπ₁⟩ := h₁
      obtain ⟨zU, gU, hzU, hgU, hzU_epi, heU⟩ := hH U p q
      obtain ⟨zV, gV, hzV, hgV, hzV_epi, heV⟩ := hH V p q
      have := hzU_epi
      have := hzV_epi
      exact normalized_homology_naturality g (p + q)
        (U.obj.filtration.complexCycles p (p + q) 1)
        (V.obj.filtration.complexCycles p (p + q) 1) zU zV gU gV
        (hzU.trans hgU.symm) (hzV.trans hgV.symm)
        (cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))))
        (cokernel.π (Subobject.ofLE _ _ (hBZ V p q 1 (by omega))))
        (eH U p q).hom (eH V p q).hom heU heV kz₁ k₁ hkz₁ hπ₁
    · obtain ⟨zU, gU, hzU, hgU, hzU_epi, heU⟩ := hQ U p q r hr
      obtain ⟨zV, gV, hzV, hgV, _, heV⟩ := hQ V p q r hr
      have := hzU_epi
      have hg_n := congrArg (fun f ↦ f.f (p + q)) hg
      have ha_n := congrArg (fun f ↦ f.f (p + q)) ha
      have hzρ : zU ≫ kz = ρ ≫ zV := by
        apply (cancel_mono (V.obj.filtration.complexCycles p (p + q) r).arrow).1
        rw [Category.assoc, hkz, ← Category.assoc, hzU, Category.assoc]
        rw [show (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ≫
            g.f (p + q) = (s p).f (p + q) ≫
              (V.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) from hg_n]
        rw [← Category.assoc, ← hρ, Category.assoc, ← hzV, ← Category.assoc]
      have hgρ : gU ≫ HomologicalComplex.cyclesMap a (p + q) = ρ ≫ gV := by
        apply (cancel_mono
          ((V.obj.filtration.complexQuotient p (p + r) (by omega)).iCycles (p + q))).1
        rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, hgU,
          Category.assoc]
        rw [show (U.obj.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) ≫
            a.f (p + q) = (s p).f (p + q) ≫
              (V.obj.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) from ha_n]
        rw [← Category.assoc, ← hρ, Category.assoc, ← hgV, ← Category.assoc]
      have hw : a ≫ φ V p r hr = φ U p r hr ≫ b := by
        have : Epi (U.obj.filtration.complexQuotientπ p (p + r) (by omega)) := by
          dsimp [DecreasingFiltration.complexQuotientπ]
          infer_instance
        apply (cancel_epi (U.obj.filtration.complexQuotientπ p (p + r)
          (show p ≤ p + r by omega))).1
        rw [← Category.assoc, ha, Category.assoc, hφ]
        rw [← Category.assoc, ← step_restriction_square U.obj.filtration
          V.obj.filtration t.hom.hom s hs (p - r + 1) p (by omega)]
        rw [Category.assoc, ← hb, ← Category.assoc, ← hφ, Category.assoc]
      exact normalized_image_naturality (p + q) a b (φ U p r hr) (φ V p r hr) hw
        ρ zU zV gU gV
        (cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)))
        (cokernel.π (Subobject.ofLE _ _ (hBZ V p q r hr)))
        (eQ U p q r hr).hom (eQ V p q r hr).hom heU heV kz k hzρ hgρ hk


/-- The page-core witnesses can be chosen with their actual successor isomorphisms uniquely
normalized on successor-cycle representatives. The global comparisons `eZ` are also used
in the image-comparison representative equation. No cochain-degree bound is imposed.
Source: Stacks Project, Homology, Tags 012K, 012M and 012O.
(blueprint: lem-kun-filtered-page-functor-normalized).

Proof:
1. Apply lem-sp-filtered-quotient-comparisons to the supplied transition maps and their
projection equations. Obtain boundary containments and normalized first-page comparisons.
Use lem-sp-filtered-complex-page-differential for the representative differentials.
2. Apply lem-sp-filtered-quotient-page-maps to these differentials. Its four squares
specify the filtered-map action; its identity and composition equations give the page laws.
3. Choose the unique successor isomorphisms of lem-sp-filtered-complex-normalized-homology.
The epic covers from lem-sp-filtered-complex-successor-cycles-cover show that successor
representatives are cycles, and their homology classes map to their successor quotient
classes. The universal normalization square and uniqueness give the displayed equivalence.
4. Use lem-sp-filtered-quotient-homology-naturality to assemble these pages and successor
isomorphisms into one functor. Take its quotient-page comparisons to be identities.
5. Use lem-sp-filtered-complex-quotient-image-comparison for eI. Its transition equals the
supplied map by cancellation of the epic source projection. The representative projection
is epic by lem-sp-filtered-complex-representative-epis, fixing its normalization.
6. For a filtered map use lem-sp-filtered-quotient-map-restrictions and the four squares
of lem-sp-filtered-quotient-page-maps. Cancel monic cycle inclusions to compare restrictions,
then cancel the epic representative projection and quotient projection for eI naturality.
7. At page one take e1 from lem-sp-filtered-quotient-comparisons. Comparing its representative
normalization with lem-sp-filtered-complex-quotient-image-comparison and cancelling the
representative epimorphism gives the first-page image equation and first-page naturality.
8. Apply lem-sp-filtered-quotient-canonical-structure to this same functor and e1. The
representative differential gives d1 and the exact couple with the stated map equations.
9. Apply lem-sp-bounded-filtered-couple-abutment to these witnesses for the cohomology
filtration, alpha-colimits, cocone equation, convergence and infinite-page comparison.
10. Choose filtration indices a,b with F(a)=top and F(b)=bottom. For fixed p choose
R=max(1,b-p,p+1-a). Beyond R the cycle and boundary formulas are constant, and the
outgoing target and incoming source lie outside the filtration support. Their differentials
vanish, and all later quotient pages identify with the stationary quotient. This uses
only filtration bounds, and applies to complexes unbounded in either cochain direction. -/
theorem boundedFilteredComplex_pageFunctor_normalized
    (C : Type u) [Category.{v} C] [Abelian C]
    (φ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
        U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
    (hφ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ φ U p r hr =
          Subobject.ofLE (U.obj.filtration.step p)
            (U.obj.filtration.step (p - r + 1))
            (U.obj.filtration.antitone_step (by omega)) ≫
              U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)) :
    ∃ (S : ObjectProperty.FullSubcategory
          (fun U : FilteredObject (CochainComplex C ℤ) ↦ U.filtration.IsFinite) ⥤
        CohomologicalSpectralSequence C 1)
      (e₁ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        ((S.obj U).page 1).X (p, q) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
      (eI : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).page r hr).X (p, q) ≅
          image (HomologicalComplex.homologyMap (φ U p r hr) (p + q)))
      (hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (_hr : 1 ≤ r),
        U.obj.filtration.complexBoundaries p (p + q) r ≤
          U.obj.filtration.complexCycles p (p + q) r)
      (eZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (hBZ U p q r hr))),
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (hr : 1 ≤ r),
        (∃ (hZ : U.obj.filtration.complexCycles p (p + q) (r + 1) ≤
              U.obj.filtration.complexCycles p (p + q) r)
            (f : (U.obj.filtration.complexCycles p (p + q) (r + 1) : C) ⟶
              ((S.obj U).page r hr).cycles (p, q)),
          Epi f ∧ f ≫ ((S.obj U).page r hr).iCycles (p, q) =
            Subobject.ofLE _ _ hZ ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫
              (eZ U p q r hr).inv) ∧
        ∀ e : ((S.obj U).page r hr).homology (p, q) ≅
            ((S.obj U).page (r + 1) (by omega)).X (p, q),
          (∀ (hZ : U.obj.filtration.complexCycles p (p + q) (r + 1) ≤
                U.obj.filtration.complexCycles p (p + q) r)
              (f : (U.obj.filtration.complexCycles p (p + q) (r + 1) : C) ⟶
                ((S.obj U).page r hr).cycles (p, q)),
            f ≫ ((S.obj U).page r hr).iCycles (p, q) =
                Subobject.ofLE _ _ hZ ≫
                  cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫
                    (eZ U p q r hr).inv →
              f ≫ ((S.obj U).page r hr).homologyπ (p, q) ≫ e.hom ≫
                  (eZ U p q (r + 1) (by omega)).hom =
                cokernel.π (Subobject.ofLE _ _ (hBZ U p q (r + 1) (by omega)))) ↔
            e = (S.obj U).iso r (r + 1) (p, q) rfl hr) ∧
      (∀ (U V : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (t : U ⟶ V) (p q r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).iso r (r + 1) (p, q) rfl hr).hom ≫
            ((S.map t).hom (r + 1) (by omega)).f (p, q) =
          HomologicalComplex.homologyMap ((S.map t).hom r hr) (p, q) ≫
            ((S.obj V).iso r (r + 1) (p, q) rfl hr).hom) ∧
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        (eI U p q 1 (by omega)).hom ≫
            image.ι (HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) =
          (e₁ U p q).hom ≫
            HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) ∧
      (∀ (U V : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (t : U ⟶ V) (p q r : ℤ) (hr : 1 ≤ r),
        ∃ (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex C ℤ) ⟶
            (V.obj.filtration.step a : CochainComplex C ℤ))
          (a : U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
            V.obj.filtration.complexQuotient p (p + r) (by omega))
          (b : U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) ⟶
            V.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
          (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p),
          (∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
            (U.obj.filtration.step i).arrow ≫ t.hom.hom) ∧
          U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ a =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + r) (by omega) ∧
          U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ≫ b =
            s (p - r + 1) ≫
              V.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ∧
          U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
          ((S.map t).hom 1).f (p, q) ≫ (e₁ V p q).hom =
            (e₁ U p q).hom ≫ HomologicalComplex.homologyMap g (p + q) ∧
          ((S.map t).hom r hr).f (p, q) ≫ (eI V p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ V p r hr) (p + q)) =
            (eI U p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ≫
                HomologicalComplex.homologyMap b (p + q)) ∧
      ∀ U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite),
        (∀ p q : ℤ,
          ∃ (i : U.obj.filtration.gradedPiece (p + 1) ⟶
              U.obj.filtration.complexQuotient p (p + 2) (by omega))
            (j : U.obj.filtration.complexQuotient p (p + 2) (by omega) ⟶
              U.obj.filtration.gradedPiece p)
            (hij : i ≫ j = 0) (hS : (ShortComplex.mk i j hij).ShortExact),
            U.obj.filtration.complexQuotientπ (p + 1) (p + 1 + 1) (by omega) ≫ i =
              Subobject.ofLE (U.obj.filtration.step (p + 1))
                (U.obj.filtration.step p) (U.obj.filtration.antitone_step (by omega)) ≫
                  U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ∧
            U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ≫ j =
              U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
            ((S.obj U).page 1).d (p, q) (p + 1, q) ≫ (e₁ U (p + 1) q).hom =
              (e₁ U p q).hom ≫
                hS.δ (p + q) (p + 1 + q) (by simp [ComplexShape.up]; omega)) ∧
        (∀ (p q r : ℤ) (hr : 1 ≤ r),
          ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
              (U.obj.filtration.complexCycles p (p + q) r : C))
            (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
              (U.obj.filtration.complexQuotient p (p + r) (by omega)).cycles (p + q)),
            z ≫ (U.obj.filtration.complexCycles p (p + q) r).arrow =
              (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
                (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
            g ≫ (U.obj.filtration.complexQuotient p (p + r) (by omega)).iCycles (p + q) =
              (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
                (U.obj.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) ∧
            z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫
                (eZ U p q r hr).inv ≫
                (eI U p q r hr).hom ≫
                image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) =
              g ≫ (U.obj.filtration.complexQuotient p (p + r) (by omega)).homologyπ
                (p + q) ≫ HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ∧
        (∃ (G : ∀ n : ℤ, DecreasingFiltration (U.obj.obj.homology n))
          (X : BigradedExactCouple C 0) (L : X.LimitSubobjects)
          (A : ∀ n : ℤ, X.AlphaColimit n)
          (aH : ∀ n : ℤ, (A n).obj ≅ U.obj.obj.homology n)
          (eD : ∀ P Q : ℤ, X.D P Q ≅
            (U.obj.filtration.step (-Q) : CochainComplex C ℤ).homology (P + Q))
          (eC : ∀ (s : ℕ) (p q : ℤ),
            (X.pageCouple s).E (2 * p + q) (-p) ≅
              ((S.obj U).page (s + 1) (by omega)).X (p, q)),
          (∀ n p : ℤ, (G n).step p =
            imageSubobject (HomologicalComplex.homologyMap
              (U.obj.filtration.step p).arrow n)) ∧
          (∀ n : ℤ, (G n).IsFinite ∧ (G n).IsSeparated) ∧
          (∀ n P : ℤ,
            (A n).ι P ≫ (aH n).hom =
              (eD P (n - P)).hom ≫ eqToHom (by
                rw [show -(n - P) = P - n by omega, show P + (n - P) = n by omega]) ≫
                HomologicalComplex.homologyMap
                  (U.obj.filtration.step (P - n)).arrow n) ∧
          (∀ P Q : ℤ,
            X.alpha P Q ≫ (eD (P - 1) (Q + 1)).hom =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (Subobject.ofLE (U.obj.filtration.step (-Q))
                  (U.obj.filtration.step (-(Q + 1)))
                  (U.obj.filtration.antitone_step (by omega))) (P + Q) ≫
                eqToHom (by rw [show P - 1 + (Q + 1) = P + Q by omega])) ∧
          (∀ P Q : ℤ,
            X.initialG P Q ≫ eqToHom (by congr 1 <;> omega) ≫
                (eC 0 (-Q) (P + 2 * Q)).hom ≫ (e₁ U (-Q) (P + 2 * Q)).hom ≫
                eqToHom (by
                  rw [show -Q + (P + 2 * Q) = P + Q by omega]
                  rfl) =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (U.obj.filtration.complexQuotientπ (-Q) (-Q + 1) (by omega)) (P + Q)) ∧
          (∀ (s : ℕ) (p q : ℤ),
            (eC s p q).hom ≫
                ((S.obj U).page (s + 1) (by omega)).d (p, q)
                  (p + (s + 1), q - (s + 1) + 1) =
              (X.pageCouple s).d (2 * p + q) (-p) ≫
                eqToHom (by congr 1 <;> omega) ≫
                  (eC s (p + (s + 1)) (q - (s + 1) + 1)).hom) ∧
          X.ConvergesTo L A ∧
          (∀ p q : ℤ, Nonempty
            (X.pageInfinity L (2 * p + q) (-p) ≅ (G (p + q)).gradedPiece p))) ∧
        (∀ p q : ℤ, ∃ (R : ℤ) (hR : 1 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
          U.obj.filtration.complexCycles p (p + q) r =
            U.obj.filtration.complexCycles p (p + q) R ∧
          U.obj.filtration.complexBoundaries p (p + q) r =
            U.obj.filtration.complexBoundaries p (p + q) R ∧
          ((S.obj U).page r (by omega)).d (p, q) (p + r, q - r + 1) = 0 ∧
          ((S.obj U).page r (by omega)).d (p - r, q + r - 1) (p, q) = 0 ∧
          Nonempty (((S.obj U).page r (by omega)).X (p, q) ≅
            ((S.obj U).page R hR).X (p, q))) := by
  classical
  let hBZ := fun (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (_hr : 1 ≤ r) ↦
    filteredComplex_boundaries_le_cycles U.obj.obj U.obj.filtration p (p + q) r
  obtain ⟨eH, eQ, hQ, hH, hfirst, hmaps⟩ := normalizedPage_comparisons C φ hφ hBZ
  let D := fun (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (r : ℤ) (hr : 1 ≤ r) ↦
    (filteredComplex_page_differential_exists_unique U.obj.obj U.obj.filtration r hr).choose
  obtain ⟨m, ⟨hid, hcomp, hm⟩, _⟩ := filteredQuotient_page_maps D
  have hex := fun U r hr pq ↦
    filteredComplex_normalized_homology U.obj.obj U.obj.filtration r hr (D U r hr) pq
  choose e he using fun U r hr pq ↦ (hex U r hr pq).exists
  let E (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) :
      CohomologicalSpectralSequence C 1 :=
    { page := fun r hr ↦ (D U r hr).page
      iso := fun r r' pq hrr' hr ↦ e U r hr pq ≪≫
        eqToIso (congrArg (fun s ↦
          filteredComplexPageObject U.obj.obj U.obj.filtration s pq) hrr') }
  let S : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite) ⥤
      CohomologicalSpectralSequence C 1 :=
    { obj := E
      map := fun {U V} t ↦
        { hom := fun r hr ↦ m t r hr
          comm := fun r r' pq hrr' hr ↦ by
            subst r'
            simpa only [E, Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id] using
              filteredQuotient_homology_naturality D m hm e he U V t r hr pq }
      map_id := fun U ↦ by
        apply SpectralSequence.hom_ext
        intro r hr
        exact hid U r hr
      map_comp := fun {U V W} t t' ↦ by
        apply SpectralSequence.hom_ext
        intro r hr
        exact hcomp U V W t t' r hr }
  refine ⟨S, eH, eQ, hBZ, (fun U p q r hr ↦ Iso.refl _), ?_, ?_, hfirst, ?_, ?_⟩
  · intro U p q r hr
    have hZ := filteredComplex_cycles_successor_le U.obj.obj U.obj.filtration r (p, q)
    obtain ⟨f, hfepi, hf⟩ := filteredComplex_successor_cycles_cover
      U.obj.obj U.obj.filtration r hr (D U r hr) (p, q) hZ
    constructor
    · exact ⟨hZ, f, hfepi, by
        dsimp only [S, E, FilteredComplexPageDifferential.page, filteredComplexPageObject,
          filteredComplexPageπ] at hf ⊢
        simpa only [Iso.refl_inv, Category.comp_id] using hf⟩
    · intro e'
      dsimp only [S, E, FilteredComplexPageDifferential.page, filteredComplexPageObject]
      simp only [Iso.refl_inv, Iso.refl_hom, Category.comp_id]
      change FilteredComplexHomologyNormalized U.obj.obj U.obj.filtration r
        (D U r hr) (p, q) e' ↔ e' = _
      simp only [eqToIso_refl, Iso.trans_refl]
      exact ⟨fun hn ↦ (hex U r hr (p, q)).unique hn (he U r hr (p, q)),
        fun h ↦ h ▸ he U r hr (p, q)⟩
  · intro U V t p q r hr
    exact ((S.map t).comm r (r + 1) (p, q) rfl hr).symm
  · intro U V t p q r hr
    obtain ⟨s, a, b, g, kz, k, hs, ha, hb, hg, hkz, hk, h₁, hn₁, hnQ⟩ :=
      hmaps U V t p q r hr
    obtain ⟨kz₁, k₁, hkz₁, hk₁⟩ := h₁
    have hkpage := hm U V t r hr p q s g kz k hs hg hkz hk
    have hkpage₁ := hm U V t 1 (by omega) p q s g kz₁ k₁ hs hg hkz₁ hk₁
    exact ⟨s, a, b, g, hs, ha, hb, hg,
      hkpage₁ ▸ hn₁ k₁ ⟨kz₁, hkz₁, hk₁⟩, hkpage ▸ hnQ⟩
  · intro U
    have hd : ∀ (p q p' q' r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).page r hr).d (p, q) (p', q') ≫ (Iso.refl _).hom =
          (Iso.refl _).hom ≫ (D U r hr).d (p, q) (p', q') := by
      intros
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    obtain ⟨hd₁, X, eD, eC, hα, hγ, hdC⟩ :=
      filteredQuotient_canonical_structure C hBZ eH hH U (S.obj U)
        (fun p q r hr ↦ Iso.refl _) (D U) hd
    dsimp only [S, E, FilteredComplexPageDifferential.page, filteredComplexPageObject] at hγ
    simp only [Iso.trans_hom, Iso.refl_hom, Category.id_comp] at hγ
    obtain ⟨G, L, A, aH, hG, hfinite, hcocone, hconv, hinf⟩ :=
      boundedFilteredComplex_coupleAbutment C S eH U X eD eC hα hγ
    refine ⟨?_, ?_, ⟨G, X, L, A, aH, eD, eC, hG, hfinite, hcocone,
      hα, hγ, hdC, hconv, hinf⟩, ?_⟩
    · simpa only [Iso.refl_trans] using hd₁
    · intro p q r hr
      obtain ⟨z, g, hz, hg, _, heQ⟩ := hQ U p q r hr
      exact ⟨z, g, hz, hg, by
        dsimp only [S, E, FilteredComplexPageDifferential.page, filteredComplexPageObject]
        simpa only [Iso.refl_inv, Category.id_comp] using heQ⟩
    · have hpages (p q r : ℤ) (hr : 1 ≤ r) :
          ∃ h : U.obj.filtration.complexBoundaries p (p + q) r ≤
              U.obj.filtration.complexCycles p (p + q) r,
            Nonempty (((S.obj U).page r hr).X (p, q) ≅ cokernel (Subobject.ofLE _ _ h)) :=
        ⟨hBZ U p q r hr, ⟨Iso.refl _⟩⟩
      intro p q
      obtain ⟨R₀, hR₀, hsub⟩ :=
        pageCore_subobjects_stabilize U.obj.filtration U.property p (p + q)
      obtain ⟨R₁, hR₁, hdiff⟩ := pageCore_differentials_stabilize U (S.obj U) hpages p q
      let R := max R₀ R₁
      have hR : 1 ≤ R := hR₀.trans (le_max_left _ _)
      have hR₀R : R₀ ≤ R := le_max_left _ _
      have hR₁R : R₁ ≤ R := le_max_right _ _
      refine ⟨R, hR, ?_⟩
      intro r hr
      obtain ⟨hZr, hBr⟩ := hsub r (hR₀R.trans hr)
      obtain ⟨hZR, hBR⟩ := hsub R hR₀R
      have hZ := hZr.trans hZR.symm
      have hB := hBr.trans hBR.symm
      obtain ⟨hout, hin⟩ := hdiff r (hR₁R.trans hr)
      obtain ⟨equot⟩ := pageCore_quotient_iso
        (hBZ U p q r (hR.trans hr)) (hBZ U p q R hR) hB hZ
      exact ⟨hZ, hB, hout, hin, ⟨equot⟩⟩

end CategoryTheory
