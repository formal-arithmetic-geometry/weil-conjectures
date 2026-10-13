/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.Algebra.Homology.HomologySequence
/-!
# Exact-couple comparison for representative quotient differentials

Source: Stacks Project, Tag 012K, cycle-boundary construction and first differential.
(blueprint: lem-sp-filtered-quotient-canonical-structure).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

/-- Identify canonical quotient differentials with the filtered homology exact couple.
Source: Stacks Project, Tag 012K, Lemma 12.24.2 and the first differential in 12.24.3;
blueprint thm-sp-spectral-object-yields, construction steps 1--2.
(blueprint: lem-sp-filtered-quotient-canonical-structure).

Proof. Form the short exact sequence F^(p+1) to F^p to gr^p at every p.
Its long exact homology sequence supplies D(P,Q)=H^(P+Q)(F^(-Q)),
E(P,Q)=H^(P+Q)(gr^(-Q)), alpha the inclusion map, initialG the quotient map,
and f the connecting map. Exactness of the long exact sequence gives all three
exact-couple axioms. Derive this couple repeatedly. The representative calculation
of the derived E terms gives Z_(s+1)/B_(s+1) at (P,Q)=(2p+q,-p).
For each derivation its differential is induced by x to dx: lifting a class along
inclusions and applying the connecting map differentiates its representative.
Its kernel is the image of successor cycles modulo current boundaries, and its
incoming image is successor boundaries modulo current boundaries. The abelian
quotient-of-quotients comparison gives the next derived E term. This induction
identifies every derived differential with D, and the hypothesis hd transports
these comparisons to the specified pages of E. No homology comparison chosen
inside E is used by this assertion.
At page one hH identifies eH with the canonical graded homology comparison:
the representative projection z and the cokernel projection are epic, so their
composite cancels from the comparison equation. The short exact sequence
gr^(p+1) to F^p/F^(p+2) to gr^p has maps fixed by the two projection squares.
Its connecting homomorphism differentiates a lifted representative. Thus it is
D at page one; hd gives the first displayed differential equation. The original
couple uses actual inclusion and quotient maps, so alpha and initialG have the
stated equations. Composing the canonical derived comparisons with eZ inverse
gives eC and its differential equation, with the displayed index transports. -/
theorem filteredQuotient_canonical_structure
    (C : Type u) [Category.{v} C] [Abelian C]
    (hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r)
    (eH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
    (hH : ∀ (U : ObjectProperty.FullSubcategory
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
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
    (E : CohomologicalSpectralSequence C 1)
    (eZ : ∀ (p q r : ℤ) (hr : 1 ≤ r),
      (E.page r hr).X (p, q) ≅ cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)))
    (D : ∀ (r : ℤ) (hr : 1 ≤ r),
      FilteredComplexPageDifferential U.obj.obj U.obj.filtration r)
    (hd : ∀ (p q p' q' r : ℤ) (hr : 1 ≤ r),
      (E.page r hr).d (p, q) (p', q') ≫ (eZ p' q' r hr).hom =
        (eZ p q r hr).hom ≫ (D r hr).d (p, q) (p', q')) :
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
            (E.page 1).d (p, q) (p + 1, q) ≫
                (eZ (p + 1) q 1 (by omega) ≪≫ eH U (p + 1) q).hom =
              (eZ p q 1 (by omega) ≪≫ eH U p q).hom ≫
                hS.δ (p + q) (p + 1 + q) (by simp [ComplexShape.up]; omega)) ∧
        (∃ (X : BigradedExactCouple C 0)
          (eD : ∀ P Q : ℤ, X.D P Q ≅
            (U.obj.filtration.step (-Q) : CochainComplex C ℤ).homology (P + Q))
          (eC : ∀ (s : ℕ) (p q : ℤ),
            (X.pageCouple s).E (2 * p + q) (-p) ≅
              (E.page (s + 1) (by omega)).X (p, q)) ,
          (∀ P Q : ℤ,
            X.alpha P Q ≫ (eD (P - 1) (Q + 1)).hom =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (Subobject.ofLE (U.obj.filtration.step (-Q))
                  (U.obj.filtration.step (-(Q + 1)))
                  (U.obj.filtration.antitone_step (by omega))) (P + Q) ≫
                eqToHom (by rw [show P - 1 + (Q + 1) = P + Q by omega])) ∧
          (∀ P Q : ℤ,
            X.initialG P Q ≫ eqToHom (by congr 1 <;> omega) ≫
                (eC 0 (-Q) (P + 2 * Q)).hom ≫
                (eZ (-Q) (P + 2 * Q) 1 (by omega) ≪≫
                  eH U (-Q) (P + 2 * Q)).hom ≫
                eqToHom (by
                  rw [show -Q + (P + 2 * Q) = P + Q by omega]
                  rfl) =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (U.obj.filtration.complexQuotientπ (-Q) (-Q + 1) (by omega)) (P + Q)) ∧
          (∀ (s : ℕ) (p q : ℤ),
            (eC s p q).hom ≫
                (E.page (s + 1) (by omega)).d (p, q)
                  (p + (s + 1), q - (s + 1) + 1) =
              (X.pageCouple s).d (2 * p + q) (-p) ≫
                eqToHom (by congr 1 <;> omega) ≫
                  (eC s (p + (s + 1)) (q - (s + 1) + 1)).hom)) := by sorry

end CategoryTheory
