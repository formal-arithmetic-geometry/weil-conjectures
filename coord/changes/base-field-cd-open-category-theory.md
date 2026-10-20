# AlgebraicGeometry.ProEtale.cohomologicalDimension_baseField proof namespace

## Reason

The proof applies the identity morphism of `Spec K` to the comparison theorem. The identity
notation requires `open CategoryTheory`; this command is added in the item module's namespace.
No declaration signature or public definition changes.

## Old

The item namespace had no `open CategoryTheory` command.

## New

The item namespace contains:

```lean
open CategoryTheory
```

The proof then uses `(𝟙 _)` for the identity scheme morphism.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension | C2 | Proof elaboration only; theorem signature unchanged. |

## Status

landed 20261020T230723-L-604969 2026-10-20 (merge of deliver/C2/Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension)
