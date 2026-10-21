## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitPresentation.lean`
from the exact quarantine archive named in `coord/rework.tsv`. Replaced its public
import of the withdrawn empty Sheaf stalk-condition module by
`WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`, which
provides the existing additive tensor-pullback instance and pinned derived counit.
Both definition bodies, signatures and docstrings are preserved verbatim.

The original archive failed with a missing tensor-pullback additivity instance and
unknown `SingleComplexBaseChange.counit`. The repaired module compiles without
errors or warnings through `lcompile.py` (4.1 seconds). Original archived consumer
modules `StandardSingleFlatCounitLocalizationData` and
`StandardSingleFlatCounitLocalizationPair` compile unchanged against it (3.6 and
4.1 seconds). The original `StandardSingleFlatCounitAffine` consumer also
compiles unchanged (42.1 seconds). A separate `#print axioms` probe reports
exactly `propext`, `Classical.choice`, and `Quot.sound` for both definitions.
The import-direction check permits the new provider. The full
consumer inventory is in the change record. Scratch consumer checks are outside
the delivered `lean/` tree.

The two definition nodes retain their attachments, exact statements and empty
proof plans: `def-pc-standard-single-flat-counit-presentation` and
`def-pc-standard-single-flat-counit-presentation-on-open`. Their existing dependency
node already names the adopted upstream counit provider. No node update, new node,
consumer adaptation or source-library modification is needed.

Change record:
`coord/changes/B3-standard-single-flat-counit-presentation-upstream-import.md`.

## Proved and sorry left

This assigned definition repair has zero original holes and zero remaining holes.
`AlgebraicGeometry.StandardSingleFlatCounitPresentation` and
`AlgebraicGeometry.StandardSingleFlatCounitOnOpen` are restored as concrete Prop
valued definitions. Neither contains `sorry` or chooses data from an unproved
existence assertion. No theorem hole is counted as closed: holes closed none;
holes added none; split-off statements none; every `sorry` left in this packet none.

## No longer needed

Removed the obsolete public import
`Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`, now an empty
withdrawn module, replacing it with its adopted upstream provider. All other
imports support the existing definitions and remain. No mathematical node,
obligation, unit step or consumer is pruned. The quarantine archive is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with holes, but this assigned rework
item consists of two definitions and has zero holes. The archive predates the
landed retirement of the duplicate Sheaf stalk-condition implementation. Merely
copying it back would leave the module unbuildable. The current DAG dependency
attachment is already correct; only the archived Lean import was stale.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
