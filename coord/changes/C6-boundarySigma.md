# AlgebraicGeometry.Etale.boundarySigma

## Reason

Use the already constructed canonical descended Koszul symmetry
`derivedTensorSymmetry` directly. Its involutivity theorem proves the two cancellations
in the normalization calculation. This replaces extraction from the HEq-characterized
existence theorem by the actual construction of that same signed symmetry.
Definitions used by the targets have changed implementation, so their statement-meaning
review must be reopened. No source-library declaration is changed.

## Old

```lean
def boundarySigma (T : Scheme.{u}) (M N : DerivedCategoryModule A T) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj M).obj N ≅
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj N).obj M :=
  (etaleKoszulSymmetry A T).choose M N
```

## New

```lean
def boundarySigma (T : Scheme.{u}) (M N : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u
  + 1} A))) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj M).obj N ≅
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj N).obj M :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).app M).app N
```

## Users

There are no current downstream textual users of these definitions according to
`tools/downstream.py --uses`. The pending parent is quarantined at
`quarantine/Sheaf/SixFunctors/BoundaryDualityDischarge.lean` (recorded in coord/rework.tsv),
and is unclaimed. It imports this item but does not mention the changed definitions.
Its DAG attachment and proof dependencies remain intact.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.BoundaryAlphaNormalization | C6 | Canonical formulas factored through real categorical constructions. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed; quarantined | Same hypotheses and conclusions; no direct uses of the changed declarations. |

## Status

landed 20261021T005730-L-1886275 2026-10-21 (merge of deliver/C6/Sheaf.SixFunctors.BoundaryAlphaNormalization)
