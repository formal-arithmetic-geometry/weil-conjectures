## What changed

Replaced the proof of `WeilConjectures.qcqsCompactSupport_strictReductionComparison`
by a real existential assembly from two strictly smaller named subclaims. Added
`Sheaf.Paper.QcqsCompactSupportStrictReductionData` for the strict map `β` and its
finite-coordinate equation, and `Sheaf.Paper.QcqsCompactSupportStrictReductionGamma`
for `γ` and its native total-limit projection equation. The parent node's proof
metadata now records these two dependencies.

## Proved and sorry left

The original target theorem is closed by existential elimination and conjunction
introduction. Two strictly smaller proof obligations are split off and remain as
`sorry`:

- `WeilConjectures.qcqsCompactSupport_strictReductionData`, node
  `lem-qcqs-compact-support-strict-reduction-data`;
- `WeilConjectures.qcqsCompactSupport_strictReductionGamma`, node
  `lem-qcqs-compact-support-strict-reduction-gamma`.

No sorry occurs in a definition or private declaration. This is a decomposition of
one upper hole into two proper parts of its construction.

## No longer needed

No existing import, module, or DAG node is withdrawn. The three public imports of the
item remain necessary for its statement. The parent proof now depends on the two new
subclaims; their declared proof dependencies are retained in the DAG for the workers
who prove them.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan requires substantial strict-resolution and derived-limit
constructions that are not available as a single proved declaration. The plan was
therefore split at its two independent outputs (`β` with its finite coordinates and
`γ` with its limit projections). No target statement or definition was changed.

## New nodes

`lem-qcqs-compact-support-strict-reduction-data` records construction of the strict
proper/open map and its finite-coordinate identity in
`Sheaf.Paper.QcqsCompactSupportStrictReductionData`.

`lem-qcqs-compact-support-strict-reduction-gamma` records construction of the native
 total-limit comparison and its projection identity in
`Sheaf.Paper.QcqsCompactSupportStrictReductionGamma`.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
