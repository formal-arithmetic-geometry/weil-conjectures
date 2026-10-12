# CategoryTheory.Functor.leftDerived_inverts (public imports)

## Reason

The completed proof constructs its comparison using limit cones. It no longer uses
`leftDerived_value_morphism`, so retaining its public import would retain an unused
proof route. The unchanged statement needs only the multiplicative-system definitions.
This changes reexports, not any declaration signature or definition.

## Old

```lean
public import Sheaf.CategoryTheory.LeftDerivedValueMorphism
import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
```

## New

```lean
public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.LeftDerivedExactWhenDefined | unclaimed | Direct importer; already explicitly imports LeftDerivedValueMorphism and the definitions module. Its statement and available declarations remain unchanged; no adaptation. |

All further importers obtain the removed declarations through that direct importer's
independent import of `LeftDerivedValueMorphism`; no adaptation is forced.
No statement, definition or elaborated signature is changed, so no target meaning changes.

## Status

landed 20261012T144158-L-2111996 2026-10-12 (merge of deliver/W3/Sheaf.CategoryTheory.DerivedFunctorInverts)
