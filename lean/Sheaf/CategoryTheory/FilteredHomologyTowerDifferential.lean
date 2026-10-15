/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.FilteredHomologyCoupleData
import WeilConjectures.Algebra.Homology.ExactCouple.Basic

/-! # Representative comparisons with the canonical exact-couple tower

Source: Stacks Project, Tags 012K and 011R.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

/-- The canonical derived-couple differential differentiates simultaneous filtered
representatives. The maps into the tower are fixed by their initial-homology
normalization; no quotient isomorphism is supplied or asserted here.
Source: Stacks Project, Tag 011R, derived-map restriction equations, and Tag 012K,
Lemma 12.24.2, differential on representatives.
(blueprint: lem-sp-filtered-homology-tower-differential).

Proof. At zero, the connecting homomorphism for F^(p+1) into F^p sends the
homology class of a lifted graded cycle to the homology class of its differential.
Compose with the graded projection; hH identifies this with the prescribed
initial quotient class. For the successor, restrict a representative whose
differential lies in F^(p+s+2) to the preceding differential kernel. The
restriction equation for derived f identifies its image with the lifted
connecting class in the image of alpha. The restriction equation for derived g
then projects that class onto the next cycle quotient. These equations give
exactly the class of the differentiated representative. Induction and the
canonical tower projection recurrence preserve the equation. The normalization
through the monic tower inclusions uniquely determines the t maps, and the
monic graded-cycle inclusions uniquely determine j, so the calculation holds
for every supplied family satisfying those equations. The two arithmetic
transports merely reindex the same source and target objects. -/
theorem filteredHomology_tower_differential
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
    (j : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        (U.obj.filtration.gradedPiece p).cycles (p + q))
    (tQ : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
          s (2 * p + q) (-p) : C))
    (hj : ∀ (s : ℕ) (p q : ℤ),
      j s p q ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
        (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow)
    (ht : ∀ (s : ℕ) (p q : ℤ),
      tQ s p q ≫
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
            s (2 * p + q) (-p)).arrow ≫
          (filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom =
        j s p q ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (s : ℕ) (p q : ℤ)
    (A : C)
    (a : A ⟶ (U.obj.filtration.step p : CochainComplex C ℤ).X (p + q))
    (a' : A ⟶ (U.obj.filtration.step (p + (s + 1)) :
      CochainComplex C ℤ).X (p + (s + 1) + (q - (s + 1) + 1)))
    (x : A ⟶ (U.obj.filtration.complexCycles p (p + q) (s + 1) : C))
    (y : A ⟶ (U.obj.filtration.complexCycles (p + (s + 1))
      (p + (s + 1) + (q - (s + 1) + 1)) (s + 1) : C))
    (ha : a ≫ (U.obj.filtration.step p).arrow.f (p + q) ≫
      U.obj.obj.d (p + q) (p + (s + 1) + (q - (s + 1) + 1)) =
      a' ≫ (U.obj.filtration.step (p + (s + 1))).arrow.f
        (p + (s + 1) + (q - (s + 1) + 1)))
    (hx : x ≫ (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow =
      a ≫ (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q))
    (hy : y ≫ (U.obj.filtration.complexCycles (p + (s + 1))
      (p + (s + 1) + (q - (s + 1) + 1)) (s + 1)).arrow =
      a' ≫ (U.obj.filtration.complexQuotientπ (p + (s + 1))
        (p + (s + 1) + 1) (by omega)).f
          (p + (s + 1) + (q - (s + 1) + 1))) :
    x ≫ tQ s p q ≫
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
          s (2 * p + q) (-p) ≫
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).d
          (2 * p + q) (-p) ≫
        eqToHom (congrArg₂
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).E
          (show 2 * p + q + 2 + s =
            2 * (p + (s + 1)) + (q - (s + 1) + 1) by omega)
          (show -p - 1 - s = -(p + (s + 1)) by omega)) =
      y ≫ tQ s (p + (s + 1)) (q - (s + 1) + 1) ≫
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
          s (2 * (p + (s + 1)) + (q - (s + 1) + 1)) (-(p + (s + 1))) := by sorry

end CategoryTheory
