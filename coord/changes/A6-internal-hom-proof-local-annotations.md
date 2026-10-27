# AlgebraicGeometry.ProEtale.CondensedRing.internalHom_stability

## Reason

The completed assembly initially typechecked in 87.4 seconds. Profiling found most
proof cost in type checking large derived-operation expressions. Local irreducibility
and explicit tensor equations reduced the clean focused compile to 51.9 seconds.
The static interface scanner flags these local commands, so this record documents
their scope. No signature, definition body, attribute visible to importers, or public
import is changed.

## Old

No local reducibility annotations; the original proof body was `by sorry`.

## New

The original signature is unchanged. Private proof imports and
`open CategoryTheory.Pretriangulated.Opposite` support the assembly.
The new annotations are:

```lean
attribute [local irreducible] upperStarFromPoint relativeInternalHomDual
attribute [local irreducible] derivedTensor
```

They affect elaboration in this file only. The Tor test explicitly simplifies
`derivedTensor` and `CategoryTheory.MonoidalCategory.curriedTensor_obj_obj`.
No consumer adaptation is required: every existing declaration and its type and
public visibility remains identical, and no annotation is exported.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | A6 | proof completed from four smaller obligations |
| All importers of this module | unchanged | identical public interface; no adaptation |

## Status

landed 20261025T201322-L-2420949 2026-10-25 (merge of deliver/A6/Sheaf.Paper.DetThmSfCtfStabilityInternalHom)
