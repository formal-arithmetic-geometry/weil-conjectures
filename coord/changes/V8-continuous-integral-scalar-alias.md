# AlgebraicGeometry.ProEtale.CondensedRing.integralScalarExtension

## Reason

Withdrawn by the reviewer (2026-10-25): no change. The delivery proposed turning
this literal derived-functor alias from `def` into `abbrev`, claiming that
`continuousScalarDerivedEncoding` exceeds the 60-second limit with the semireducible alias.
The reviewer compiled the delivered proof against the unchanged sheaf-dag
`Sheaf.Paper.ContinuousIntegralCoefficientData` (`def`). It compiled in 18.4 s, with axioms
`propext`, `Classical.choice`, `Quot.sound`. With the `abbrev` it took 18.3 s. The adaptation is
therefore unnecessary, and `Sheaf.Paper.ContinuousIntegralCoefficientData` is delivered
identical to sheaf-dag. This record documents the withdrawal only.

## Old

```lean
noncomputable def integralScalarExtension (X : Scheme.{u}) :=
  L(Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X))
```

## New

Unchanged (identical to Old):

```lean
noncomputable def integralScalarExtension (X : Scheme.{u}) :=
  L(Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X))
```

## Users

No user is affected: the declaration, its transparency and its module are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousIntegralCoefficientData | unclaimed | Unchanged (delivered identical to sheaf-dag). |
| Sheaf.Paper.ContinuousScalarDerivedEncoding | V8 | Uses the unchanged `def`; compiles. |

## Status

landed 20261025T011044-L-3638669 2026-10-25 (merge of deliver/V8/Sheaf.Paper.ContinuousScalarDerivedEncoding)
