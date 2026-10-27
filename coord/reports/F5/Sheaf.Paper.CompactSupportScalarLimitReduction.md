## What changed

Proved `WeilConjectures.PurStrictScalar.scalarCompletion_existsUnique` by applying
`WeilConjectures.PurStrictScalar.completedScalarBalancing_existsUnique` to the
already fixed `scalarCompletionOrdinary` comparison.

The new, completely proved helper is in
`Sheaf.Paper.CompletedScalarLocalizationBalancing`. It detects exactness of
completed scalar extension after conservative restriction to constant coefficients,
using the given ordinary balancing and exact finite-free constant scalar extension.
It then applies the existing proved `exactScalarCochainIso` and
`localizedBalancing` helpers to obtain the cochain-counit equation and uniqueness.
Its exactness and additivity arguments are supplied by the item's existing
instances. The zero complex and identity coefficient extensions are included.

The helper is a separate module to meet the 60-second limit per file. The
foundational prefix is also moved verbatim to
`Sheaf.Paper.CompactSupportScalarLimitFoundations`; the item re-exports it with
a public import. The scalar-completion proof belongs to this foundational prefix.
Existing public names, signatures, non-theorem definition bodies, and original
public imports are preserved. Local unfolding settings and sequential elaboration
reduce the checking cost. The existing definitions node's Lean attachment is
updated, and the change record documents the move.
Updated Step 3, its dependencies, and the proof origin of
`lem-pur-compact-support-scalar-limit-reduction` to follow the proof.

Validation: all three delivery modules and all ten current direct importers of
`Sheaf.Paper.CompactSupportScalarLimitReduction` compile against this delivery
under the standard per-file limit. The consumer files required no changes and
their temporary sandbox copies were removed. Textual comparison finds no missing
original declaration or changed declaration signature after the file split.

## Proved and sorry left

Closed 1 of the 6 original holes:
`WeilConjectures.PurStrictScalar.scalarCompletion_existsUnique`.
Added 0 holes and split off 0 unproved statements.

The new helper
`WeilConjectures.PurStrictScalar.completedScalarBalancing_existsUnique` is also
proved in full; its module has 0 holes.

The five unchanged holes are listed below. The first two are now in the
foundation module and attached to `def-pur-compact-support-scalar-limit-maps`;
the final three remain in the item and attached to
`lem-pur-compact-support-scalar-limit-reduction`:

- `WeilConjectures.PurStrictScalar.scalarLimitTensor_exact`.
- `WeilConjectures.PurStrictScalar.scalarLimitRestriction_exact`.
- `WeilConjectures.PurStrictScalar.scalarRoosNormalization`.
- `WeilConjectures.PurStrictScalar.scalarRoosTensorNormalization`.
- `WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction`.

## No longer needed

None. No original imports, modules, declarations, or DAG dependencies are removed.
The remaining theorem holes retain the existing route and dependencies. The
unit's realized route stays unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The finite-level
`localizedBalancing` proof already supplies the localization and uniqueness
argument needed here, once completed extension is proved exact. Factoring this
argument into a proved helper module makes the compilation cost independent of
the remainder of the scalar-limit module.

The rework table lists this module as quarantined in an earlier build. Its
current source exists and is preserved; this delivery neither withdraws the
module nor removes its Lean attachments.

## New nodes

`lem-pur-completed-scalar-localization-balancing`, realized by
`Sheaf.Paper.CompletedScalarLocalizationBalancing`, records localization of any
given ordinary completed/constant balancing with its precise complex-counit
normalization. Its sole public theorem is proved; this introduces no new hole.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
