## What changed

Withdraw Sheaf.AlgebraicGeometry.ArbitraryBaseFiniteP1Integrals under dispatched brief
step 8d: no current Lean module imports it or uses any of its seven declarations.
The withdrawal is listed in deleted.txt; deliver3.py installs the empty module.
Set the matching node's lean field to null and explain the withdrawal in proof_origin.
The mathematical arbitrary-base statement and its seven-step proof are retained.
No unit statement, unit step, target, consumer, or other module is changed.
The change record is coord/changes/S9-withdraw-unused-arbitrary-base-finite-p1-integrals.md.

## Proved and sorry left

This is pruning, not a proof or decomposition: 0 of 1 holes proved, 0 split off,
0 holes added. The one removed hole is
AlgebraicGeometry.Etale.exists_arbitraryBaseFiniteP1Integrals
(node lem-sp-tower-p1-arbitrary-base-integrals). No sorry remains in the withdrawn
module, and no other Lean module is included in this delivery. This removes an
unused whole-library hole; it does not claim a reduction in the targets' closure,
because the item is already outside that closure.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.ArbitraryBaseFiniteP1Integrals, with all seven
unused declarations: arbitraryBaseFiniteP1DiagonalTrace,
ArbitraryBaseFiniteP1ChernFamily, ArbitraryBaseFiniteP1SplittingFamily,
ArbitraryBaseFiniteP1SplittingSpec, ArbitraryBaseFiniteP1BaseChange,
ArbitraryBaseFiniteP1DiagonalIntegrals, exists_arbitraryBaseFiniteP1Integrals
(all in namespace AlgebraicGeometry.Etale).

Withdrawal removes the module's public imports OrdinaryFiniteP1Data and
ProjectiveLineDiagonalIntegrals and proof imports OrdinaryFiniteP1Adjunction,
ProjectiveLineTrace, ProperUnboundedBaseChange, ProjectiveSpaceStandardCharts,
RingedToposDerivedPushforwardComposition, EffectiveCartier, Pullbacks and
Adjunction.Mates. No dependency module is claimed globally pruned: those results
have independent consumers. The arbitrary-base DAG result remains a planned input
to det-sp-tower-p1-adjunction, which has no Lean attachment. Its mathematical proof
plan and dependencies stay; this delivery does not bypass that future unit route.
The unit's realized statement and all six realized step lists are empty.

## Where the brief, the DAG or earlier work was wrong

The dispatch describes this module as reached from the targets. Current sources
show no importer at all, and none of its declaration names occurs outside itself.
The node's proof_origin and J1's existing withdrawal record explain why the earlier
interface was pruned: NoetherianPrimePowerSmoothDuality needs only Noetherian
integrals and already imports ProjectiveLineDiagonalIntegrals directly. ND later
reintroduced a newly named arbitrary-base interface as a stage-2 statement, without
a Lean consumer. Keeping it would create proof work not presently used by a target.
The module is withdrawn using the brief's explicit unused-item procedure; no
mathematical statement is weakened and no theorem is claimed proved.

Searches run: LeanFinder for finite-coefficient Kummer splitting and diagonal traces
returned unrelated Weierstrass projective-curve results; Loogle found only the generic
adjunction triangle lemma; Mathlib grep found no matching declaration. Whole-library
rg found the seven names and the module import name only in the item itself.
The existing J1 withdrawal record and the ND stage-2 report were read, as were the
node and sk-prop-sp-tower-geometric unit record.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
