# WeilConjectures.CompletedQuotient.completedComparisonScalarLimitImage

## Reason

The proof needs to evaluate finite expression syntax at constructors and to reason about
scalarQuotients, without unfolding the larger primitive realizations. The command comparison
records local transparency changes as interface edits, so they are recorded explicitly here.
All changes are local to the assigned module. Existing public theorem signatures, definitions,
instances, global attributes and public imports are unchanged. No other existing module changes.
The two new theorem modules carry their own new nodes and no global instances or attributes.

## Old

The local transparency setup in the assigned module was:

```lean
attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substituteInputs substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction scalarQuotients
```

The theorem `completedComparisonScalarLimitImage` had its present unchanged signature and a
single sorry proof. Neither `completedScalarBetaComparison` nor
`completedScalarRouteCoordinates` existed.

## New

The local transparency setup is:

```lean
attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction
```

After the existing transparency options, the proof additionally uses:

```lean
attribute [local implicit_reducible] substituteInputs
attribute [local implicit_reducible] value expression IntegralCoherence.value scalarQuotients
  sourceExpression targetExpression
```

The original theorem is proved from the existing normalization lemmas and the two new,
strictly smaller uncancelled comparison equations. Those equations are declared in
`Sheaf.Paper.CompletedScalarBetaComparison` and `Sheaf.Paper.CompletedScalarRouteCoordinates`,
with verbatim signatures recorded in their new DAG nodes. All helpers in the original module
are private and proved. The proof retains the existing respectTransparency settings.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedComparisonScalarLimitImage | H9 | Local proof setup and proof only; public statement unchanged. |
| Sheaf.Paper.CompletedComparisonQuotientRealization | unclaimed in shared snapshot | Direct importer; same public theorem signature and public imports. No adaptation needed. |
| Sheaf.Paper.CompletedPullbackTensorConstruction | unclaimed in shared snapshot | Direct importer; same public theorem signature and public imports. No adaptation needed. |
| Sheaf.Paper.CompletedScalarBetaComparison | H9, new | New named uncancelled beta comparison statement, with its own node. |
| Sheaf.Paper.CompletedScalarRouteCoordinates | H9, new | New strict square and coordinate statement, with its own node. |

There are no changed public declaration names to require further name-based consumer adaptation.
The delivery tool checks the importers against these files. No target meaning changes, and no
source-library module is modified.

## Status

landed 20261028T081743-L-2778614 2026-10-28 (merge of deliver/H9/Sheaf.Paper.CompletedComparisonScalarLimitImage)
