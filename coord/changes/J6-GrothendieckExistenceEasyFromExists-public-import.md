# AlgebraicGeometry.grothendieckExistenceEasy_exists_from

## Reason

Restore the public interface of the source currently preserved in quarantine.
The rework row reports unknown public `Scheme`; compiling a fresh copy also
reports unknown public `IsNoetherian`. Both declarations, together with the
coherent formal module and completion API, are exposed by the defining module
already imported privately. Promoting that import repairs elaboration of the
unchanged public signature.

This retry addresses the stale-base return for head `c6958b233b`, whose base
was `6488bba00`. It starts from the current quarantined source, reproduces the
actual compiler errors and reapplies the correction there.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
```

The public import precedes the private proof imports. All declarations,
signatures, docstrings and proof bodies remain verbatim from the current
quarantine source. No target statement or definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists | J6 | Restored; public signature elaborates. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy | quarantined | Unchanged consumer compiled against repair; no adaptation. |

The parent above is the sole direct importer found in the active library and
quarantine. It retains its theorem and its use of the unchanged item theorem.
It was copied into the sandbox for compilation only and is not delivered.

## Status

landed 20261020T145520-L-2405821 2026-10-20 (merge of deliver/J6/Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists)
