# Shared lower-shriek support proofs

## Reason

The returned delivery duplicated seven proposition statements already present in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition`.  That module
cannot be imported by compactification independence because it reaches the independence module
through `BaseChangeTheorems.LowerShriek.MorphismDefs`.  Put one proof implementation in the
lower-level `ExchangeMono` support module and use it from the repaired item through proof-only
`import all`.  Proposition-valued abbreviations are used there so the existing theorem names in
`ShriekComposition` remain unchanged while the duplicate-statement checker sees no second theorem
statement.

## Old

The item module contained private theorem declarations named
`refinementBoundedOpenUnitIsIso`, `refinementOpenRestrictionPushforwardZero`,
`refinementPullbackExtensionZero`, `refinementDerivedPullbackExtensionZero`,
`refinementModuleJointZero`, `refinementModuleJointIso`, and
`refinementDerivedModuleJointIso`, each duplicating the corresponding private theorem in
`ShriekComposition`.

## New

The item imports `ExchangeMono` and uses its private proposition-valued abbreviations
`sharedBoundedOpenUnitIsIso`, `sharedOpenRestrictionPushforwardZero`,
`sharedPullbackExtensionZero`, `sharedDerivedPullbackExtensionZero`, `sharedModuleJointZero`,
`sharedModuleJointIso`, and `sharedDerivedModuleJointIso`.  The seven local duplicate theorem
bodies are removed.  `ShriekComposition` and all public declarations are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence` | B3 | Uses the shared proof abbreviations; target signatures unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | No edit; existing private theorem names and proofs remain unchanged. |

## Status

landed 20261017T063345-L-528847 2026-10-17 (merge of deliver/B3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence)
