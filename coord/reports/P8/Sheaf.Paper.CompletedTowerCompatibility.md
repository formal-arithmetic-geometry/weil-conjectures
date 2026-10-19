## What changed

Proved `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourTowers_compatibility`
with its original signature. The evaluation clause is the evaluation conjunct of
existing `strictTowerExchangeMateNormalization`; the strict rectangle is cancellation
of `towerH` with its inverse; the endomorphism clause is existing
`exchangeStrict_naturality` specialized to an endomorphism.

Moved the five unchanged tower definitions (`fourTowerCorners`, `towerH`, `towerH'`,
`towerV`, `towerV'`) into `Sheaf.Paper.CompletedTowerCorners`, publicly reexported by
the item. Changed `Sheaf.Paper.CompletedBaseChangeMap` to import that definition
module. This removes the artificial import cycle through CompletedBaseChangeMap
and permits use of the already stated stronger normalization theorem. This is a
separation of definitions from their theorem, not a compile-time workaround.
No definition body, existing signature, hypothesis, or target changes.

Updated the compatibility proof plan and the two consumers' statement citations and
dependencies to refer to the separate definition node. These are citation repairs;
the mathematical statements and every Lean signature are unchanged. The existing normalization module is
untouched. The change record is
`coord/changes/P8-completed-tower-definitions.md`.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourTowers_compatibility`
(node `lem-weil-pbc-tower-compatibility`). No sorry remains in any delivered Lean
module. Added zero holes; split off zero unproved statements.

The existing theorem `AlgebraicGeometry.Scheme.strictTowerExchangeMateNormalization`
(node `lem-weil-pbc-strict-tower-exchange-mate-normalization`) remains unproved in its
own unchanged module. This delivery uses its stated evaluation conjunct as intended
by stage 3, and does not claim to close that dependency or the target axiom closure.
`exchangeStrict_naturality` is already proved in the current source.

## No longer needed

Removed the item's proof-only imports:
`Sheaf.Paper.AdicCoefficientDatum`, `Sheaf.Paper.FourCorners`,
`Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange`,
`Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`,
`Sheaf.Paper.CondensedAmbientExchange`, `Sheaf.Paper.FiniteLevelRectangle`, and
`Sheaf.Paper.PerfectProjectionFormula`.
The former public imports `Sheaf.Paper.FourArrows` and
`Sheaf.Paper.CompletedDirectImageLimits` move to CompletedTowerCorners and remain
publicly available through it. CompletedBaseChangeMap no longer imports
CompletedTowerCompatibility; it needs only the unchanged definitions.

The compatibility proof no longer directly uses the former proof dependencies
`def-weil-pbc-ambient-ringed-exchange`, `def-weil-pbc-projection-formula-map`,
`lemma-weil-pbc-perfect-projection-formula`, or `lem-weil-pbc-finite-level-rectangle`.
The finite rectangle and its coefficient normalization remain in the proof plan
of the stronger normalization theorem. No unit statement or unit step is bypassed.
No whole module is asserted to leave the targets' import closure.

The earlier sandbox's finite-rectangle and evaluation decompositions are not part
of this delivery: the existing normalization statement already supplies the needed
clause. Their scratch files are retained outside the delivery's lean directory.

## Where the brief, the DAG or earlier work was wrong

The earlier report described a finite-rectangle split whose module was no longer
present. It did not describe the retained Lean proof and has been replaced.
The obstacle to the shortest route was organizational: the stronger theorem's
statement imported the same tower definitions through the compatibility module.
Extracting those definitions, with all names and bodies preserved, makes the route
acyclic. The stronger theorem and its proof do not use fourTowers_compatibility.

Read the current blueprint tower-compatibility statement and the existing stronger
normalization signature. The latter contains the exact finite evaluation clause,
including all four edge equations and the retained witnesses. The rectangle proof
uses only isomorphism cancellation. Its naturality specialization imposes no added
hypothesis. Identity squares, zero objects, and zero coefficient rings require no
additional assumption in these three operations.

## New nodes

`def-weil-pbc-completed-four-towers` attaches the five existing, unchanged strict
tower constructions to their new definition-only module. It introduces no new
mathematical construction and no proof hole. The source is the four tower objects
and arrows in the blueprint tower-compatibility argument. Its source, searches,
Lean declarations, and creation metadata are recorded in the node. The two existing
consumer nodes replace the old combined-node dependency by this definition node.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
