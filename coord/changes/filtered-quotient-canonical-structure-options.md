# CategoryTheory.filteredQuotient_canonical_structure

## Reason

The completed proof triggers the unused-variable linter for the original named `hr`
parameters inside two input function types. These proof parameters do not occur in
their conclusions. Preserve the exact statement and binder names, and disable that
linter only for this declaration. The added backward elaboration transparency option
supports conversion of the heterogeneous base-normalization equation. The delivery
checker classifies these option commands as an interface change and requires this
record. No object definition, theorem statement, namespace, visibility, or public
import changes. No dependent module requires an adaptation, and no target statement
changes meaning.

## Old

No added compiler-option commands. The existing declaration signature was:

```lean
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
                  (eC s (p + (s + 1)) (q - (s + 1) + 1)).hom))
```

## New

The signature is verbatim unchanged. Add
`set_option backward.isDefEq.respectTransparency false` before the universes, and
`set_option linter.unusedVariables false in` immediately before this declaration's
docstring. Its proof is now complete from the three named intermediate statements:

```lean
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
                  (eC s (p + (s + 1)) (q - (s + 1) + 1)).hom))
```

## Users

The declaration-use search finds the following existing modules. There are no
adapted modules. The new modules' definitions and statements are recorded in their
own nodes and their public declarations were not previously in the library.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure | C3 | Proof completed; signature unchanged; local compiler/linter configuration only. |
| Sheaf.CategoryTheory.FilteredQuotientPageRealization | unclaimed | None: theorem signature and all public imports stay identical. |

## Status

landed 20261013T072340-L-1115686 2026-10-13 (merge of deliver/C3/Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure)
