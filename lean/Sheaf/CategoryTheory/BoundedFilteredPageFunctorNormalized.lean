/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.CategoryTheory.BoundedFilteredComplexPageCore
public import Sheaf.CategoryTheory.FilteredComplexNormalizedHomology
import Sheaf.CategoryTheory.FilteredQuotientComparisons
import Sheaf.CategoryTheory.FilteredComplexPageDifferential
import Sheaf.CategoryTheory.FilteredQuotientPageMaps
import Sheaf.CategoryTheory.FilteredComplexSuccessorCyclesCover
import Sheaf.CategoryTheory.FilteredQuotientHomologyNaturality
import Sheaf.Algebra.Homology.FilteredComplexQuotientImageComparison
import Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis
import Sheaf.CategoryTheory.FilteredQuotientMapRestrictions
import Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure
import Sheaf.CategoryTheory.BoundedFilteredCoupleAbutment
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.Abelian.Filtration

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
  sorry

end CategoryTheory
