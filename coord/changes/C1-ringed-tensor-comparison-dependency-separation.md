# CategoryTheory.derivedPullbackComplexComparison

## Reason

The original same-universe tensor-pullback theorem still has one hole, while the
independent-universe theorem already has a complete representative-descent proof.
Its computation lemma imports the ordinary-comparison module, which publicly imports
the item. Importing that lemma directly would close a cycle. The computation lemma
uses only the complex-level counit construction from the item, not its derived
tensor-pullback theorem or ordinary tensorator structure.

Move that existing construction verbatim to
`Sheaf.Paper.DerivedPullbackComplexComparison`, publicly reexport it from the item,
and replace the computation module's broad ordinary-comparison import by its actual
statement dependencies. No definition body, existing declaration signature or theorem
statement changes. The new module is a dependency separation required by the proof,
not a file split to evade compilation limits.

The item also obtains the flatness API through the already required unit-existence
module's public reexports. The unit-existence module also publicly reexports TensorClosed.
Remove the two redundant direct imports of Flat and TensorClosed and publicly import
the unit-existence module. This keeps every previous public dependency visible.
The original direct-import combination fails against the current published compilation
with duplicate legacy/upstream declarations (`SheafOfModules.tensorClosed` and
`SheafOfModules.IsFlat`); using the existing consistent reexports avoids loading those
parallel module presentations together. All source imports still name existing modules.

## Old

In `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`:

```lean
/-- Transport the homotopy left-derived comparison to the complex localization Q.
Source: Stacks 06YY and 07A4
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def derivedPullbackComplexComparison
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    LF.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  LF.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
    epsilon.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
```

In `Sheaf.Paper.DerivedPullbackRepresentativeComputation`:

```lean
public import Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses
```

## New

The same declaration and defining expression above now live in
`Sheaf.Paper.DerivedPullbackComplexComparison`, with the minimal generic abelian-category
context; the inferred declaration type is unchanged. The item publicly imports it.
The computation module publicly imports the extracted comparison, KFlat, FlatOnSite,
AlgebraicInverseImage and the Mathlib left-derived-functor API, instead of the
ordinary-comparison module. Its existing theorem and all private proofs are unchanged.
The item's proof imports the computation lemma, proves total-tensor naturality and
uses the existing resolving-representative and tensor-descent theorems.
Proved private generic tensor-naturality and tensor-additivity lemmas avoid
repeating the corresponding arguments at each concrete sheaf-module type.
Scalar-extension uniqueness now substitutes the object equalities directly. It
reuses the existing private scalar-extensionality theorem through `import all`;
its duplicate proof and local insertion/restriction helpers have been removed.
The final unique-existence statement follows from the descent square and its
uniqueness clause; proof irrelevance identifies representative membership witnesses.
No mathematical assumptions or existing statement changes are introduced. Conversion
between site-flatness and the legacy monoidal flatness predicate is proved from
`siteSheafTensorRightIso`, without changing either predicate.

## Users

`tools/downstream.py ... --uses derivedPullbackComplexComparison` lists these 20
textual users. Every call retains the same constant and defining expression.
There are no target semantics changes and no caller adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedProjectionCoherence | T4 | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.DerivedPullbackRepresentativeComputation | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.ProjectionFormulaArrows | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.ProjectionFormulaBaseChangeNaturality | R4 | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.ProjectionFormulaFiniteFree | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.ProjectionFormulaInverseNaturality | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.ProjectionFormulaProjectiveSummand | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.ProjectionFormulaTotalization | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.RingedCoefficientProjectionCocycle | C4 | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.RingedComparisonTensorAdjunction | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.RingedExchangeTensorCoherence | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.RingedProjectionTensorComposition | V2 | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.RingedSquareTensorCompatibility | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.RingedStrictTowerProjectionMorphism | B6 | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullback | C1 (dispatched item) | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.ringedProjectionFormula_totalization_left | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.Paper.ringedProjectionFormula_totalization_right | unclaimed | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.SixFunctors.OpenTensorNormalization | U8 | Identical declaration, signature and defining expression; no caller edit. |
| Sheaf.SixFunctors.RingedDerivedMonoidalComparisons | E2 | Identical declaration, signature and defining expression; no caller edit. |

The only direct importer of `DerivedPullbackRepresentativeComputation` is
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`. It already publicly imports
`RingedTopoiCanonicalTensorComparisonOfUniverses` and `ProEtaleCanonicalTensorPullback`
on its own; none of its visible declarations is lost. It compiled unchanged
against the delivered overlay in 58.5 seconds, without errors or warnings.
The computation module is unclaimed in the shared claim snapshot and is adapted
only in its imports.

## Status

landed 20261019T231045-L-544096 2026-10-19 (merge of deliver/C1/Sheaf.Paper.RingedTopoiCanonicalTensorPullback)
