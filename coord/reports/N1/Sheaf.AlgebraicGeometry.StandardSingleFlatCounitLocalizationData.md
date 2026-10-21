## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationData.lean`
from the quarantine source named in the assigned rework row. Preserved
`AlgebraicGeometry.standardSingleFlatCounit_localization_data` with its exact
signature, visibility and docstring. Its witness is the concrete zero cochain
complex, bounded by zero. Replaced categorical-flatness conversion by Mathlib's
subsingleton-to-free-to-flat instances and removed the private proof import
`WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat`. The presentation public
import remains necessary to state the affine hypothesis.

Updated only the assigned node's proof and proof origin to describe this direct
argument. Its Lean attachment, source, statement and statement dependencies are
preserved. No other module or node is changed. Change record:
`coord/changes/N1-standard-single-flat-counit-localization-data-restoration.md`.

The server `lcompile.py` check of the restored theorem passes without warnings
(5.4 seconds). A separate axiom probe of the final declaration passes (4.4 seconds) and
reports exactly `propext`, `Classical.choice` and `Quot.sound`. The signature was compared verbatim with the archive. Downstream and text searches
cover both active and quarantined Lean sources; there are no consumers to adapt.

## Proved and sorry left

This is a restoration of an already proved theorem: zero original holes, zero
remaining holes, zero holes closed and zero holes added. The complete proof of
`AlgebraicGeometry.standardSingleFlatCounit_localization_data` is retained with
its simplified flatness argument (node
`lem-pc-standard-single-flat-counit-localization-data`). There is no `sorry` in
any delivered Lean declaration and no split-off statement or new axiom.

## No longer needed

Removed the proof-only import
`WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat`: categorical flatness is
unnecessary for a zero module, whose algebraic flatness follows from freeness.
No new proof import is needed because the required Mathlib declarations are
already public dependencies of the presentation module.

No mathematical node or module is withdrawn or claimed globally pruned. In
particular the quarantined parent still cites the assigned node in its DAG plan,
so zero current Lean importers is not used as a reason to withdraw it. The
quarantine archive is preserved. The existing empty proof-dependency list agrees
with the direct zero-complex construction. No unit statement or proof step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes holes, but the assigned archive has none. Its
source had been removed during cluster rework; this delivery restores its actual
declaration, rather than producing an empty module or deleting its attachment.
B3 has already repaired the presentation module's obsolete import, and the
original archived theorem now also compiles against that provider.

The theorem's conclusion only asks for existence of a bounded-above flat
complex; it does not identify it with a localized direct image. Thus the zero
complex proves precisely this statement, without using the affine or relative
flatness hypotheses. This limitation was already documented by earlier workers;
the present delivery does not treat it as the stronger counit-comparison result.
The pending completion node's prose still refers to this data theorem although
its archived Lean proof uses the actual localized presentation via the homology
theorem. That parent's mathematics and proof plan are outside this restoration
and are left intact for its assigned review.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
