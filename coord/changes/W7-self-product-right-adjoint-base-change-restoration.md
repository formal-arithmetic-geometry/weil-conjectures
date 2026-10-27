# AlgebraicGeometry.proper_flat_selfProduct_rightAdjoint_baseChange_local

## Reason

Restore the assigned quarantined module, preserving its existing theorem signature and
complete proof. The rework row records an unknown `derivedPullback` in the public
statement after the upstream sync. Its old public import
`Sheaf.AlgebraicGeometry.DerivedPullback` is now an empty withdrawn module. Import the
actual adopted source interface publicly, so `derivedPullback` is available both in the
statement and to consumers. This changes no mathematical definition or target meaning.
The quarantine archive and its node attachment remain intact.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

The assigned module is absent from `lean/`; the complete theorem is preserved in
`quarantine/Sheaf/AlgebraicGeometry/SelfProductRightAdjointBaseChangeLocal.lean`.
Its full theorem signature is retained verbatim in the restored module and node.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

Restore `lean/Sheaf/AlgebraicGeometry/SelfProductRightAdjointBaseChangeLocal.lean`
with its unchanged theorem signature, docstring and transport proof. Add a module docstring.
Correct the node's first proof step to name the adopted source module that supplies its
existing private `pullback_transport` helper. All four proof dependencies remain.

## Users

`tools/downstream.py` with `--allow-missing` reports zero current library importers and
zero textual consumers. A separate search of both `lean/` and `quarantine/` finds the
archived consumer below. Its call has the same arguments and expected isomorphism as
before; the restored theorem signature was compared verbatim with the archive.
No consumer adaptation is required. The archived consumer's independent quarantine
repair remains outside this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | W7 | Assigned restoration; actual public derived-pullback import repairs statement elaboration. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed in local claim snapshot; quarantined | Same theorem signature and isomorphism; no adaptation. |

## Status

landed 20261025T181254-L-4134383 2026-10-25 (merge of deliver/W7/Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal)
