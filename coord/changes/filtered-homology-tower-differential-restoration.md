# filteredHomology_tower_differential

## Reason

The returned delivery predated the independent F7 restoration of this statement.
Start from the current live statement and complete its proof. The new proof uses
the now-proved public forward representative formula, the canonical comparison
lift and the existing finite-cycle comparison. No statement, definition, public
import, visibility or meaning of a target is changed. The computation API added
in this delivery is fully proved against F8's explicit constructor.

The differential module is unclaimed; the assigned quotient module is held by M6.
No module held by another group is edited.

## Old

The current base has the following active signature, with proof `by sorry`:

```lean
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
          s (2 * (p + (s + 1)) + (q - (s + 1) + 1)) (-(p + (s + 1)))
```

## New

The same signature, verbatim, with a complete proof and proof-only imports:

```lean
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
          s (2 * (p + (s + 1)) + (q - (s + 1) + 1)) (-(p + (s + 1)))
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.FilteredHomologyTowerDifferential
--uses filteredHomology_tower_differential` lists the following eleven downstream
modules. The quotient-pages module uses the unchanged theorem signature; the
item's new proof also uses it. No existing consumer needs adaptation because
there is no interface or data-definition change.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.BoundedFilteredComplexPageCore | unclaimed | Same signature and definitions; no adaptation required. |
| Sheaf.CategoryTheory.BoundedFilteredComplexPages | unclaimed | Same signature and definitions; no adaptation required. |
| Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence | unclaimed | Same signature and definitions; no adaptation required. |
| Sheaf.CategoryTheory.BoundedFilteredPageConstruction | unclaimed | Same signature and definitions; no adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence | unclaimed | Same signature and definitions; no adaptation required. |
| Sheaf.CategoryTheory.FilteredHomologyCoupleQuotientPages | unclaimed | Same signature and definitions; no adaptation required. |
| Sheaf.CategoryTheory.FilteredHomologyTowerQuotients | M6 | Same signature and definitions; no adaptation required. |
| Sheaf.CategoryTheory.FilteredHomotopySpectralSequence | unclaimed | Same signature and definitions; no adaptation required. |
| Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure | unclaimed | Same signature and definitions; no adaptation required. |
| Sheaf.CategoryTheory.FilteredQuotientPageRealization | unclaimed | Same signature and definitions; no adaptation required. |
| Sheaf.Paper.FlatFilteredComplexComparison | unclaimed | Same signature and definitions; no adaptation required. |
| Sheaf.CategoryTheory.FilteredHomologyTowerDifferential | unclaimed | Complete the existing theorem proof; signature and visibility unchanged. |
| Sheaf.CategoryTheory.FilteredHomologyCoupleComputations | new in M6 delivery | Proved computation API; no admitted declaration. |

## Status

landed 20261018T092906-L-3441479 2026-10-18 (merge of deliver/M6/Sheaf.CategoryTheory.FilteredHomologyTowerQuotients)
