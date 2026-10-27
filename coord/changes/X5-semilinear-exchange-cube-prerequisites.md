# WeilConjectures.PodExchangeCube comparison prerequisites

## Reason

The normalized rational/common Frobenius cube equations need to be separate proof
items. They use the existing comparison types and normalization predicates, so
those prerequisites must be available without importing their assembly theorem.
Move the existing data verbatim into `Sheaf.Paper.SemilinearExchangeCubeData` and
publicly re-export it from `Sheaf.Paper.SemilinearExchangeCubeCoherence`.
This is an import-cycle refactor for a mathematical decomposition, not a response
to a compile-time limit. The original module has no current Lean importers;
its DAG parents remain supported by the identical re-exported interface.

## Old

`Sheaf.Paper.SemilinearExchangeCubeCoherence` declares `iterated`, `Equivariant`,
`twist`, `twistIso`, `relabeling`, `Comparisons`, `directExchange`, `compactExchange`,
`changedExchange`, `directComposition`, `supportTransport`, `supportComposition`,
`Laws`, `rationalPullComponent`, `rationalNormalized`, `commonPullComponent`, and
`commonNormalized` in namespace `WeilConjectures.PodExchangeCube`.
Their complete original signatures and bodies are reproduced verbatim in the
new prerequisite module. The two original coherence theorems remain in their
original module with their original signatures.

## New

`Sheaf.Paper.SemilinearExchangeCubeData` declares exactly those prerequisites,
with the same names, signatures, visibility, attributes and bodies, including
the existing proved `relabeling` theorem. The original module publicly imports
that module and retains `rational_coherence` and `common_coherence`.
The `Comparisons` docstring additionally names the new prerequisite owner node.
No operation, normalization, coefficient category, or domain is changed.
The moved declarations' signatures and all non-theorem bodies were compared
mechanically against the original and agree exactly after whitespace normalization.
The change does not alter the meaning of any target statement.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | X5 | Re-exports the identical prerequisites and assembles the component cube theorems. |
| Sheaf.Paper.SemilinearExchangeCubeData | new in this delivery | Owns the unchanged prerequisite declarations. |
| Sheaf.Paper.SemilinearRationalOrdinaryCubes | new in this delivery | Uses rational normalization and the ordinary transformations. |
| Sheaf.Paper.SemilinearCommonOrdinaryCubes | new in this delivery | Uses common normalization and the ordinary transformations. |
| Sheaf.Paper.SemilinearRationalSupportCubes | new in this delivery | Uses rational normalization and the support transformations. |
| Sheaf.Paper.SemilinearCommonSupportCubes | new in this delivery | Uses common normalization and the support transformations. |
| Sheaf.Paper.SemilinearRationalRefinementCubes | new in this delivery | Uses rational normalization and compactification comparisons. |
| Sheaf.Paper.SemilinearCommonRefinementCubes | new in this delivery | Uses common normalization and compactification comparisons. |

`tools/downstream.py Sheaf.Paper.SemilinearExchangeCubeCoherence --uses ...`
reported zero downstream Lean modules. DAG parents need no change: both public
coherence theorem signatures and the exported prerequisite interface are preserved.
No source-library module is changed and no existing module is withdrawn.

## Status

landed 20261025T164736-L-1069369 2026-10-25 (merge of deliver/X5/Sheaf.Paper.SemilinearExchangeCubeCoherence)
