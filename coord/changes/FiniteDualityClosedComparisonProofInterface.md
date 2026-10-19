# FiniteDualityClosedComparison proof interface

## Reason
The item module now contains the completed proof and imports three modules privately for proof-only declarations. The delivery also adds private helper theorems and scopes the required elaboration options to the declarations that use them. The change record documents the module-level interface check required by stage 3 because the delivery tool reports a command-level interface change while comparing the completed module against the base.

## Old
The module contained the two public theorem declarations with `sorry` proofs and no private proof helper declarations. Its public instance registration for `isIso_finiteDualityClosedComparisonDelta_proof` was already present.

## New
The same public declarations and signatures remain unchanged. Their proofs are complete. Three proof-only imports and four private helper theorems are added. The existing instance registration is unchanged. The new `set_option ... in` wrappers are scoped to individual declarations and do not alter exported declarations.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.FiniteDualityClosedComparison | D6 | The item itself receives the completed proof and private helpers; public signatures remain unchanged. |

## Status
landed 20261019T093334-L-2297055 2026-10-19 (merge of deliver/D6/Sheaf.SixFunctors.FiniteDualityClosedComparison)
