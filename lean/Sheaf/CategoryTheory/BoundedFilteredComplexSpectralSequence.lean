/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Spectral sequences of bounded filtered complexes

Source: blueprint node thm-sp-spectral-object-yields, order 515; Stacks Project,
Homology, Section 12.24 (Tag 012K), Lemmas 12.24.2--12.24.4 and 12.24.11
(blueprint: thm-sp-spectral-object-yields).

The domain is the full subcategory of filtered cochain complexes with finite filtration.
The exact-couple coordinates are `(P,Q) = (2*p+q,-p)`; its page `s+2` is filtered page `s+1`.
-/

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

/-- The bounded filtered-complex spectral sequence, including its canonical first
and image pages, convergence, and functoriality.
Source: blueprint thm-sp-spectral-object-yields, statement and six proof steps;
Stacks, Tag 012K (blueprint: thm-sp-spectral-object-yields).

Proof (postponed in stage 2).
1. The short exact sequences of filtration steps give long exact cohomology sequences
   by lem-sp-long-exact-of-triangle.
2. Their E1-indexed couple has bidegrees (-1,1), (1,0), (0,0). Reindex by
   (P,Q)=(2p+q,-p) to obtain def-sp-exact-couple's type-zero couple.
3. Derived couples and lem-sp-page-induction give the spectral sequence of
   def-sp-spectral-sequence. Standard page R is filtered page R-1. The first differential
   is the boundary of the indicated short exact sequence of quotient complexes.
4. lem-sp-filtered-complex-ZB-description gives the displayed cycles and boundaries,
   their inclusion and quotient, and the canonical cohomology-image comparison. Its
   representative equation fixes the comparison. At r=1 this is H(gr). Finite filtration
   makes the cycle and boundary tails stationary.
5. The image filtration on H(K) is finite, separated and exhaustive. The alpha-colimit
   is H(K); its filtration index P corresponds to filtered index P-n in degree n.
   Stabilization and the graded comparison give def-sp-convergence's ConvergesTo.
6. lem-sp-couple-morphism supplies compatible page maps for filtered maps. The canonical
   quotient maps and first-page maps commute with them. The extra support hypothesis
   puts E1 in the first quadrant; outgoing and incoming differentials then vanish for
   r>max(p,q)+1, giving the stated stabilization. -/
theorem boundedFilteredComplex_spectralSequence
    (C : Type u) [Category.{v} C] [Abelian C] :
    ∃ (S : ObjectProperty.FullSubcategory
          (fun U : FilteredObject (CochainComplex C ℤ) ↦ U.filtration.IsFinite) ⥤
        CohomologicalSpectralSequence C 1)
      (e₁ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        ((S.obj U).page 1).X (p, q) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
      (φ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
        U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
      (eI : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).page r hr).X (p, q) ≅
          image (HomologicalComplex.homologyMap (φ U p r hr) (p + q))),
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ φ U p r hr =
          Subobject.ofLE (U.obj.filtration.step p)
            (U.obj.filtration.step (p - r + 1))
            (U.obj.filtration.antitone_step (by omega)) ≫
              U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)) ∧
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
          ∃ (hBZ : U.obj.filtration.complexBoundaries p (p + q) r ≤
              U.obj.filtration.complexCycles p (p + q) r)
            (eZ : ((S.obj U).page r hr).X (p, q) ≅ cokernel (Subobject.ofLE _ _ hBZ))
            (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
              (U.obj.filtration.complexCycles p (p + q) r : C))
            (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
              (U.obj.filtration.complexQuotient p (p + r) (by omega)).cycles (p + q)),
            z ≫ (U.obj.filtration.complexCycles p (p + q) r).arrow =
              (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
                (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
            g ≫ (U.obj.filtration.complexQuotient p (p + r) (by omega)).iCycles (p + q) =
              (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
                (U.obj.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) ∧
            z ≫ cokernel.π (Subobject.ofLE _ _ hBZ) ≫ eZ.inv ≫
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
            ((S.obj U).page R hR).X (p, q))) ∧
        ((∀ p : ℤ, p ≤ 0 → U.obj.filtration.step p = ⊤) →
          (∀ p i : ℤ, (i < p ∨ p + 1 < i) →
            IsZero ((U.obj.filtration.gradedPiece p).homology i)) →
          (∀ (p q r : ℤ) (hr : 1 ≤ r), (p < 0 ∨ q < 0) →
            IsZero (((S.obj U).page r hr).X (p, q))) ∧
          ∀ (p q r t : ℤ) (hr : 1 ≤ r) (ht : r ≤ t), max p q + 1 < r →
            ((S.obj U).page r hr).d (p, q) (p + r, q - r + 1) = 0 ∧
            ((S.obj U).page r hr).d (p - r, q + r - 1) (p, q) = 0 ∧
            Nonempty (((S.obj U).page r hr).X (p, q) ≅
              ((S.obj U).page t (by omega)).X (p, q))) := by
  sorry

end CategoryTheory
