## Reason

Preflight found a cycle from the new finite-level node through the broad system
coefficient-projection node back to the item. The pre-existing realization definition
also pointed at all of system projection data, although it uses only constantModule.
This couples a sectionwise constant-scalar definition to unrelated compact-scalar
coherence and integral reconstruction. The mathematical and Lean signatures do not change.

## Old

The realization node's stmt_deps included def-pur-etale-system-projection-data.
The finite-level proof plan cited lem-pur-etale-system-coefficient-projection, whose
successive-coefficient coherence travels through the integral operation DAG.

## New

Add def-pur-etale-constant-module-restriction for the existing, fully constructed
AlgebraicGeometry.Etale.SystemProjection.constantModule. The realization node now
cites that precise declaration. Its statement, Lean attachment and Lean source stay
verbatim. The new finite-level proof plan uses the proper coefficient tensor-unit
isomorphism and scalar-unit equation and the open scalar-exchange unit calculation
directly, then pastes adjuncts to identify compactScalarMap. It does not use the
system projection cocycle. No old declaration or proof dependency is removed from
its original module or node.

The item also adds a local irreducibility attribute for its canonical mate, with a
proved private hom equation. This is a local proof performance change, not an
exported attribute or signature change. All new theorem modules have their own nodes.

## Users

`Sheaf.Paper.EtaleBrownGeometricComparisons` uses the same realization interface.
`Sheaf.Paper.EtaleBrownLevelComparisons`,
`Sheaf.Paper.EtaleBrownProperSingletonEvaluation`, and
`Sheaf.Paper.EtaleBrownOpenSingletonEvaluation` cite the precise realization node.
Other existing citers of def-pur-etale-brown-projection-realization keep exactly the
same statement and Lean declarations. No Lean consumer adaptation is needed;
Sheaf.Paper.EtaleBrownProjectionRealization and Sheaf.Paper.EtaleSystemProjectionData
are unclaimed completed modules and their source is not changed in this packet.

## Status

landed 20261025T180724-L-4024248 2026-10-25 (merge of deliver/H6/Sheaf.Paper.EtaleBrownGeometricComparisons)
