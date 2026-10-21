# DerivedPushforwardSquareMateUnit local irreducibility attribute

## Reason

The restored module set a local reducibility status for `derivedPullback`, but the
adopted source declaration uses `irreducible_def` and Lean rejects assigning the same
status with `attribute [local irreducible]`. Removing this redundant command is required
for the module to compile against the current source library. The theorem statement and
all public definitions remain unchanged.

## Old

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  derivedPullback DerivedCategory.Qh
```

## New

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit | P4 | The edited module itself now compiles; no public signature or declaration consumer changes. |

## Status

landed 20261021T214850-L-1873330 2026-10-21 (merge of deliver/P4/Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit)
