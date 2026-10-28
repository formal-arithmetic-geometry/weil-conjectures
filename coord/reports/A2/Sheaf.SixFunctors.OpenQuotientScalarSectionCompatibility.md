## What changed

Withdraw `Sheaf.SixFunctors.OpenQuotientScalarSectionCompatibility` via
`deleted.txt`, and detach its false theorem from
`lem-sf-open-quotient-scalar-section-compatibility` by setting `lean` to null.
The DAG node and its statement/history remain. Its proof record explains the
withdrawal rather than claiming a proof of a false statement.

The replacement constructor in
`Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData` is already fully proved
and independently reviewed in landing 20261028T020709-L-2538604. Its private
`normalizedFinite` helper constructs the normalized comparison at every level
from the generic scalar/open comparison and proves the generator equation by
inverse cancellation. The public constructor chooses those comparisons and
section equations together. Its Lean source is unchanged. The parent DAG proof
record documents this actual construction and reconciles the obsolete
obligation's withdrawal with the reviewed replacement route.

Change record: `coord/changes/open-quotient-scalar-section-withdrawal.md`.

Validation: the current `OpenTensorQuotientData` source and a packaging refactor of the already proved replacement
constructor compiled as separate files in import order, in 38.2 and 10.4 seconds,
with no warnings. The sole direct importer `OpenTensorQuotientScalarCompatibility` also compiled
unchanged against that constructor and current dependency, in 20.2
seconds. Its generator calculation still uses `ScalarCompatibility.sections`.
All temporary Lean copies, including the unnecessary packaging refactor, were
removed from the sandbox. Only the withdrawal and DAG/change records are delivered.
The initial constructor-only check saw the older published four-field record;
compiling the current two-field dependency resolved that version mismatch.

## Proved and sorry left

No false theorem is reported as proved: 0 of the item's 1 proof holes were proved.
The sole hole, in
`WeilConjectures.OpenTensorQuotient.openQuotientScalarSectionCompatibility`
(node `lem-sf-open-quotient-scalar-section-compatibility`), is removed by withdrawal
of its false, unused declaration. The existing replacement constructor
`WeilConjectures.OpenTensorQuotient.openQuotientScalarCompatibilityData`
(node `lem-sf-open-quotient-scalar-compatibility-data`) has a complete proof.
No holes are split off or added; the withdrawn module becomes an empty module
with zero `sorry`. No other Lean source changes.
This is pruning and a statement repair, not a proof of the disputed statement.

## No longer needed

Pruned module: `Sheaf.SixFunctors.OpenQuotientScalarSectionCompatibility`.
Pruned declaration:
`WeilConjectures.OpenTensorQuotient.openQuotientScalarSectionCompatibility`.
Retained but detached node:
`lem-sf-open-quotient-scalar-section-compatibility`.
The withdrawn module's public import of `OpenTensorQuotientData` disappears with
it; that data module itself is still needed and is not withdrawn.

No active DAG parent cites the withdrawn node in `stmt_deps`, `proof_deps`, or
proof-step `uses`. Its former parent now directly constructs the normalized
comparison and proves the section equation; its old `statement_change` citation
records history only. No Lean source imports this module or uses its theorem.
`tools/downstream.py` confirms zero downstream modules. No unit `realized`
entry needs it. There are no rows in `coord/rework.tsv`, so no quarantined parent
is overlooked. The same-unit scalar normalization and strict-tower argument is
preserved, including `ScalarCompatibility.sections` and its uses in
`openQuotientScalarUnitEquation`. No further node or module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original statement asserted normalization for every finite comparison,
whereas the sources construct a particular normalized comparison. Given a
normalized comparison, compose with the target functor's negation automorphism:
it remains a natural isomorphism with the stated type but negates the image of
nonzero extension generators. At odd residue characteristic (identity open over
a nonempty point, l = 3) this contradicts the requested equality. Its proof plan
therefore assumed an unstated property of `finite`.

S1 correctly marked the claim disputed but left its hole. Reviewed R3 landing
20261028T020709-L-2538604 replaced the parent construction with a complete direct
normalized existence argument and pruned all live dependencies on this item.
This delivery removes the residual false statement and reconciles its attachment
with that argument, carrying the parent record update and the complete account of the reviewed
replacement argument in this packet. The existing replacement implementation is
unchanged. No theorem is weakened, and no target or source-library signature changes.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenQuotientScalarSectionCompatibility": "fdd6fd89e33daef28207b2d920705ea5b4231ed8"}, "results": {}, "time": "2026-10-28T10:24:32+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
