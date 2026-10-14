# Scalar external cup module comparison

## Reason

Restore the three withdrawn scalar comparison modules together. The published compiled
snapshot still contains them, but current repository sources omit them. The external
comparison is proved from two existing, strictly simpler DAG comparison statements.
The separate duplicate-instance repair belongs to the holder of ModuleCupKInjectiveTarget.

## Old

The three module source files are absent from the current repository. Their unchanged
signatures are recorded in the existing three lem-sc-scalar-*-comparison/compatibility nodes.

## New

Restore `scalarExternalCup_moduleComparison`, `scalarCup_moduleCup_compatibility`, and
`scalar_moduleCohomologyPullback_comparison` with exactly those recorded signatures.
The external theorem has a complete proof; the two prerequisite theorems remain admitted.
The cup predicate is the canonical imported definition, never a local copy.
The external module publicly imports its definition module directly; both comparison
lemma imports are nonpublic. This removes the ineffective earlier public rerouting.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | U4 | restored proved reduction |
| Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility | unclaimed | restored prerequisite |
| Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison | unclaimed | restored prerequisite |

## Status

landed 20261014T013049-L-3418904 2026-10-14 (merge of deliver/U4/Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison)
