## What changed

Retired `Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift` in favor of its upstream
twin `WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorShift`, as assigned by
`coord/retire-items.tsv` and the human's 2026-10-20 hand-off. The current module bodies
are identical after their copyright comments. Migrated all seven direct consumers:
`SchemeCanonicalShiftUnitIso`, `SchemeCanonicalTensorShiftAssociator`,
`SchemeCanonicalTensorShiftAssociatorKFlatOne`, `SchemeCanonicalTensorShiftProperties`,
`SchemeCanonicalTensorShiftRightUnitor`, `SchemeTensorShiftBinaryLocalizationSquare`,
and `SchemeTensorShiftLocalizationNormalization` (all under `Sheaf.AlgebraicGeometry`).
Only the public import changes, plus a line wrap in the associator's existing private
helper signature to satisfy the 100-character limit.

Reattached node `def-sc-scheme-canonical-tensor-shift` to the upstream module and
unchanged declaration. Change record:
`coord/changes/H4-retire-scheme-canonical-tensor-shift.md`.

The sandbox-only compatibility probe proves the old and upstream structures equal
by `rfl` for independent universes and prints only the three permitted axioms.
All seven changed consumers are compiled in dependency order. The source import
closures differ only in the exchanged module, with no additional duplicate modules.

## Proved and sorry left

This is a zero-hole retirement repair: proved 0 of 0 sorries; 0 split off.
Holes closed: none. Holes added: none. Holes left in the item or delivered consumers:
none. `AlgebraicGeometry.schemeCanonicalTensorShift` is the unchanged explicit upstream
construction, and every existing proof in its seven consumers is preserved.
The sandbox equality check and both construction axiom probes succeed.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift`.
Removed its public import from all seven direct consumers and replaced each with
`WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorShift`.
No mathematical nodes or prerequisites are pruned. The node and all parent references
remain valid through the upstream Lean attachment. No unit statement or proof step
is bypassed. No upstream declaration, theorem proof or import is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a sorry obligation, but this assigned retirement
has zero holes and requires replacing the duplicate module. The retirement row's
DIFFERENT reason (changed definition) is stale: the preceding localization retirement
made the current module bodies identical. The DAG's mathematical statement is correct;
only its old Sheaf Lean attachment needed migration. The source library already
provides the shortest route, so no additional theorem or decomposition is required.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
