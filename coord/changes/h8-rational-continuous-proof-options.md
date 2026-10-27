# AlgebraicGeometry.Scheme.ContinuousRational.rationalContinuousComparisonCoherence

## Reason

In module `Sheaf.Paper.RationalContinuousComparisonCoherence`, the static preflight
classifies the changed file commands as a possible interface
change. The actual changes are file-local proof elaboration settings: remove the
inherited transparency override and use the standard project instance-search size.
The proof works with the default transparency policy. Its new private lifting
definitions are proof support only. All existing public signatures, attributes,
definitions, public imports, universe commands, namespace and open commands remain
unchanged. No target statement or the meaning of any target definition changes.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
```

## New

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed (no module claim) | Public interface unchanged; no adaptation. Compiled unchanged against this delivery as a consumer check. |

The direct importer is copied only for verification and removed from the sandbox
before delivery. No existing module besides the assigned item is delivered.

## Status

landed 20261027T094422-L-223889 2026-10-27 (merge of deliver/H8/Sheaf.Paper.RationalContinuousComparisonCoherence)
