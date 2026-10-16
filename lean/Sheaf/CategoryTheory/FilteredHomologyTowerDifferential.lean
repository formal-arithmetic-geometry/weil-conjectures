/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups V2, T2
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives
import Sheaf.CategoryTheory.DerivedCoupleExact
import Sheaf.CategoryTheory.FiniteCycleFormula
import all Sheaf.CategoryTheory.FiniteCycleDerivedComparison

/-! # Representative comparisons with the canonical exact-couple tower

Source: Stacks Project, Tags 012K and 011R.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

private theorem quotient_homology_heq
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n p' n' : ℤ) (hp : p = p') (hn : n = n') :
    HomologicalComplex.homologyMap (F.complexQuotientπ p (p + 1) (by omega)) n ≍
      HomologicalComplex.homologyMap (F.complexQuotientπ p' (p' + 1) (by omega)) n' := by
  subst p' n'
  rfl

set_option linter.unusedVariables false in
/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/ -- The canonical derived-couple differential differentiates simultaneous filtered
representatives. The maps into the tower are fixed by their initial-homology
normalization; no quotient isomorphism is supplied or asserted here.
Source: Stacks Project, Tag 011R, derived-map restriction equations, and Tag 012K,
Lemma 12.24.2, differential on representatives.
(blueprint: lem-sp-filtered-homology-tower-differential).

Proof. The ambient differential squares to zero, and the filtration inclusion is
monic, so a' lifts uniquely to a cycle b in F^(p+s+1). Obtain the canonical
monic inclusions I of the derived D objects and the concrete iterated image
lift e of alphaIter. The forward-representative theorem identifies the page f
of x with the homology class of b followed by e. The finite-cycle formula
places initial g in the tower cycles, and the proved derived-g comparison
identifies e followed by page g with this factorization followed by the tower
projection. Naturality of homologyπ for the graded projection, together with
hy, hj and ht, identifies this factorization on b with y followed by tQ.
Compose the forward equation with g and transport the integer indices to
obtain the stated differential equation. The supplied hBZ, eH and hH are
unnecessary for this direct representative calculation. - /
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
          s (2 * (p + (s + 1)) + (q - (s + 1) + 1)) (-(p + (s + 1))) := by
  sorry
-/

end CategoryTheory
