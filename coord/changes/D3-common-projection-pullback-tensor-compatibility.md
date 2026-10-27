# Common projection pullback tensor compatibility

## Reason

The delivery adds a private proof import and two public intermediate declarations used by the target proof. The declarations isolate the finite-stage representative and the normalization bridge required by the target's proof plan.

## Old

The item module imported `Sheaf.Paper.CommonProjectionTensorComparison` and `WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate`, and `commonProjectionPullbackTensorCompatibility` had a `sorry` proof.

## New

The item module additionally imports `Sheaf.Paper.CommonProjectionPullbackTensorRepresentative` privately and proves `commonProjectionPullbackTensorCompatibility` by applying `projectionTensorComparisonCompatible_of_representative_formula`. The new representative module proves `canonicalCommonStagePullbackTensor_formula`; the item module records the normalization bridge theorem with its finite-stage representative hypothesis.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.CommonProjectionProperTensorCompatibility` | J2 | Compiles against the target theorem and the new helper declaration. |
| `Sheaf.Paper.CommonProjectionProperFactor` | unclaimed | Compiles against the target theorem and the new helper declaration. |
| `Sheaf.Paper.HigherTensorIdentityComposition` | unclaimed | Compiles against the unchanged target interface. |
| `Sheaf.Paper.ProjectionIdentityTensorUnit` | unclaimed | Compiles against the unchanged target interface. |
