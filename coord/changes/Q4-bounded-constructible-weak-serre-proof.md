# AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_of_weakSerre

## Reason

The assigned upstream module retains a false arbitrary-ring triangulatedness assertion.
Its signature is outside the approved upstream-statement exceptions and cannot be changed
under this assignment. Mark that declaration STATEMENT-DISPUTED, and finish the existing
true weak Serre theorem in the unclaimed companion module. This is partial progress;
it does not prove or replace the disputed assertion.

## Old

The existing theorem in `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible` ended in:

```lean
    [ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R)] :
    (boundedConstructible R).IsTriangulated := by
  sorry
```

## New

The signature, attributes, public imports and definition of bounded constructibility
are identical. The proof unfolds the conjunction to the intersection of boundedness
with the derived homology property. The existing weak Serre and intersection instances
then prove the goal:

```lean
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).IsTriangulated
  infer_instance
```

The source module receives only a dispute comment at the false instance. No interface
changes, new declarations, definition changes or consumer adaptations occur.

## Users

There is no change to what importers see. This is an independent proof completion in
an unclaimed module, permitted by the brief's unclaimed-module rule; it is not a forced
adaptation of another group's module. The proof uses only the existing imports.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory | Q4 | Dispute marker only; original hole retained. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible | unclaimed | Complete the existing weak Serre theorem proof. |

## Status

landed 20261021T111454-L-161424 2026-10-21 (merge of deliver/Q4/WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory)
