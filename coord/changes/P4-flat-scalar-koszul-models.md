# CategoryTheory.FlatScalarKoszul.limitComparison

## Reason

The finite strict calculation must be independent of the derived-limit comparison.
Move the existing strict coordinate and restriction definitions to
`Sheaf.CategoryTheory.FlatScalarKoszulModels`, publicly re-exported by the original
module. Names, visibility, universes, objects and maps are preserved. This permits
the separate `StrictScalarKoszulComparison` module without an import cycle.

Also give `limitComparison` an explicit type with the separate complex functors.
The inferred type used the complex functors of the composed ordinary functors.
Although definitionally equal, it caused rewriting to unfold the chosen limits
(`getLimitCone`) repeatedly, and caused instance/unification timeouts. The body is
unchanged; the explicit type presents the same map at its intended endpoints.

## Old

Defined in `Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison`:

```lean
def limitComparison {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :=
  letI : PreservesLimitsOfSize.{0, 0} (restriction φ) :=
    preservesSmallestLimits_of_preservesLimits (restriction φ)
  NatTrans.mapHomologicalComplex
    (preservesLimitNatIso (restriction φ) (J := ℕᵒᵖ)).hom (.up ℤ)
```

The same file also defined `Modules`, `Towers`, `tensor`, `one`, `degree`,
`factorBasis`, `positiveBasis`, `dualCoordinate`, `coordinate`, `restriction`,
`restrictComplex`, `restrictTower`, `restrictTowerComplex`, `imageSections`, and
`limitComplex` in `CategoryTheory.FlatScalarKoszul`.

## New

Defined in `Sheaf.CategoryTheory.FlatScalarKoszulModels`, with a public import in
the original module:

```lean
def limitComparison {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    limitComplex B ⋙ restrictComplex φ ⟶ restrictTowerComplex φ ⋙ limitComplex R :=
  letI : PreservesLimitsOfSize.{0, 0} (restriction φ) :=
    preservesSmallestLimits_of_preservesLimits (restriction φ)
  NatTrans.mapHomologicalComplex
    (preservesLimitNatIso (restriction φ) (J := ℕᵒᵖ)).hom (.up ℤ)
```

All the other listed declarations retain their names and bodies verbatim. Their docstrings
now attach them to the supporting definitions node.
Their original public exports remain available to importers of the item module.
The main theorem has exactly its original statement. No mathematical hypothesis,
conclusion or construction changes, and no target statement changes meaning.
The independent reader can check the two definitions by definitional equality.

## Users

`tools/downstream.py Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison --uses
CategoryTheory.FlatScalarKoszul.limitComparison` reported zero downstream modules
and one use module, the item itself. A project search also found no other Lean
importer of the item. Its unfinished DAG parent remains attached and is not withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison | P4 | Publicly imports the moved definitions; proves the unchanged comparison from them. |
| Sheaf.CategoryTheory.FlatScalarKoszulModels | P4, new | Houses the existing strict constructions; explicit limitComparison type. |
| Sheaf.CategoryTheory.StrictScalarKoszulComparison | P4, new | States the finite strict comparison without derived assumptions. |

## Status

landed 20261021T134522-L-1295510 2026-10-21 (merge of deliver/P4/Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison)
