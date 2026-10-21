# AlgebraicGeometry.Etale.boundaryProjection

## Reason

Factor the canonical etale construction through `CategoryTheory.BoundaryData` and
its explicit functor interfaces. This keeps the actual functors and maps while making
kernel conversion tractable. The independent Hom chain remains independent of alpha;
alpha remains the tensor-Hom transpose of the specified q/r/evaluation pairing.
No source-library declaration is changed and no arbitrary existence witness is chosen.
The public theorem retains the original hypotheses and all three conclusions, factored
through an explicit proposition definition. Definitions used by the targets
have changed implementation, so their statement-meaning review must be reopened.

## Old

```lean
def boundaryProjection (B : DerivedCategoryModule A Z) (M : DerivedCategoryModule A T) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj
      (R(lowerStar (ModuleCat.{u + 1} A) i).obj B)).obj M ⟶
      R(lowerStar (ModuleCat.{u + 1} A) i).obj
        (((derivedTensor (ModuleCat.{u + 1} A) Z).obj B).obj
          (L(upperStar (ModuleCat.{u + 1} A) i).obj M)) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) i).app B).app M
```

## New

```lean
def boundaryProjection (B : (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))) (M
  : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))) :
    boundaryMorphism A T
      (((boundaryData A i).Q.obj ((boundaryData A i).F.obj B)).obj M)
      ((boundaryData A i).F.obj
        (((boundaryData A i).P.obj B).obj ((boundaryData A i).L.obj M))) :=
  (boundaryData A i).projection B M
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
