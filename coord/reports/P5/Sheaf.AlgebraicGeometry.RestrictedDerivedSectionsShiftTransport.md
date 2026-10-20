## What changed

Retired `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport`, the listed
retirement item, in favor of the already proved adopted source module
`WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport`.
The public declaration
`AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedDerivedSections_shiftTransport`
has a textually identical signature in both files. `deleted.txt` withdraws only the
Sheaf duplicate. The node `lem-sbc-restricted-derived-sections-shift-transport` now
attaches to the retained source theorem, and its proof description records the source's
canonical derived-adjunction-unit calculation. No Lean source-library file is edited.

Change record:
`coord/changes/P5-restricted-derived-sections-shift-transport-retirement.md`.

## Proved and sorry left

Original item: zero holes. Holes closed: zero. Holes added: zero. Holes left: zero.
No decomposition or new intermediate theorem.

The retained declaration
`AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedDerivedSections_shiftTransport`
is already fully proved. A remote `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The original and retained public signatures were
compared verbatim. Remote single-file compilation from unchanged source copies passed
for the source twin (25.9 s), `RestrictedDerivedSectionPullbackCommShift` (17.6 s), and
`RestrictedDerivedSectionShiftComparison` (47.9 s), with no warnings. The additional
unchanged `RawFixedDerivedComparisonNaturality` source check reached the 60-second
limit, including on a single-file retry. That file already imports the source twin,
has no dependency on the withdrawn Sheaf module, and is not changed by this packet. Its existing compiled private-helper
uses remain untouched. The theorem axiom check also passed without warnings (2.4 s).
A separate `example` with the original theorem statement was proved by exact application
of the source theorem and compiled without warnings (8.2 s). This checks the actual
replacement under Lean elaboration as well as textual signature equality.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport`.
Its private `restrictedCommShiftLowerStar` instance and duplicate private proof helpers
are removed with it. The retained source proof proves the canonical adjunction unit's
shift compatibility directly, so it needs no replacement for that private instance.

Imports removed with the withdrawn module:

- public `WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison`;
- proof `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift`;
- proof `WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`.

These dependencies remain available wherever the source library requires them; no other
module is withdrawn or claimed as pruned. No mathematical node or proof dependency is
removed. The two DAG parents continue to need this same node, now realized upstream.
Their current source modules already import the retained theorem or its private helpers;
no parent adaptation is needed. Searches of the live library and quarantine find zero
remaining imports of the withdrawn Sheaf module. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a hole-bearing item, but this assignment is a listed
retirement with zero holes. The retirement row's DIFFERENT classification concerns only
the private `restrictedCommShiftLowerStar` instance; it does not identify a public API
difference. The source twin supplies the same public theorem with an independent direct
proof of canonical adjunction shift compatibility. The DAG attachment was stale and
still named the duplicate; it is migrated rather than removed. The two parents already
use the source library, including its private helpers through `import all`, so none of
their dependency edges is discarded. There is no current return or quarantine row for
this item.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
