# AlgebraicGeometry.Etale.compactSupport_unbounded_amplitude

## Reason

Two imported instances give different shift structures for the ordinary etale derived
pushforward. The original statement elaborates with the generic right-derived-functor
structure. During proof elaboration, the competing etale-specific structure causes an
instance mismatch for `IsTriangulated`. Scope the competing instances out for this theorem
with `attribute [-instance] ... in`, and infer the triangulated composite using the generic
functor explicitly. This command affects only the following declaration, and the original
elaborated signature, public imports, and exported instance attributes stay unchanged.
The static preflight asks for a change record for this scoped command.

## Old

The declaration was preceded by no scoped instance command; its proof was `by sorry`.
The two imported global instance names are:

```lean
AlgebraicGeometry.Etale.commShiftRightDerivedLowerStar
AlgebraicGeometry.Etale.isTriangulated_rightDerivedLowerStar
```

## New

```lean
attribute [-instance] commShiftRightDerivedLowerStar isTriangulated_rightDerivedLowerStar in
```

The command scopes over the existing theorem declaration and its complete proof.
No global instance is removed or changed. No definition is changed.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.EtaleCompactSupportUnboundedAmplitude
--uses compactSupport_unbounded_amplitude` reports zero downstream modules and only the
item itself as a textual user. The DAG attachment and its unfinished parents remain.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleCompactSupportUnboundedAmplitude | E3 | Theorem-scoped proof elaboration; identical signature and public imports; full proof compiles. |

No consumer adaptation is needed. No target statement uses a changed definition.

## Status

landed 20261023T102633-L-2939784 2026-10-23 (merge of deliver/E3/Sheaf.AlgebraicGeometry.EtaleCompactSupportUnboundedAmplitude)
