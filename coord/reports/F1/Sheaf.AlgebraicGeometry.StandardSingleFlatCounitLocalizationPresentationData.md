## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationPresentationData.lean`
verbatim from the quarantine source specified by its current rework row. This
restores both proved private helpers and
`AlgebraicGeometry.standardSingleFlatCounit_localization_presentation_data`.
The presentation predicate and top-open comparison dependencies are already
restored by B3 and C4. The item's public import, private proof import, theorem
signature, docstrings and proof are unchanged. The quarantine archive is intact.

The existing proof realizes every step of the DAG: choose affine S and V around
g(a) and a; verify restriction-flatness on affine sections; apply the affine
hypothesis on the top open of the restricted source; compose the two comparison
isomorphisms and their equations. All choices remain inside the existential
proof. Empty A makes the pointwise assertion vacuous; zero modules and empty
source opens are covered by the same flatness and functorial calculations.

The restored item compiles cleanly in 7.8 seconds. The unchanged archived direct
consumer `StandardSingleFlatCounitLocalization` compiles in 5.1 seconds. A separate
`#print axioms` probe compiles in 2.0 seconds and reports exactly `propext`,
`Classical.choice` and `Quot.sound`. The original and restored item are byte
identical; the module has no line over 100 characters. The change record is
`coord/changes/F1-standard-single-flat-counit-localization-presentation-data-restoration.md`.

## Proved and sorry left

Zero of zero existing sorries closed; zero holes added; zero split off; no sorry
remains in the restored module. This is a restoration of the already proved
`AlgebraicGeometry.standardSingleFlatCounit_localization_presentation_data`, not
new hole-closing progress. Both private helper proofs are also restored intact.
No new declarations or nodes are introduced.

## No longer needed

None. Both imports are used: `StandardSingleFlatCounitPresentation` supplies the
statement predicates, and `StandardSingleBaseChangeTopRestriction` supplies the
comparison used in the final proof step. The same DAG dependencies and unit route
are retained. No Lean file or DAG node is withdrawn or pruned.

LeanFinder and Loogle searches and the launcher grep search were run. LeanFinder
returned flat scheme-morphism lemmas, not relative-flatness or local counit
presentation statements; Loogle and the launcher grep returned no hits. Repository
search found related private flatness helpers and the more specialized affine
spectrum-chart theorem `isFlatOver_affineOpenRestriction`; none requires replacing
the already compiling proof.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined zero-hole restoration, not an unproved theorem. The
current rework row identifies the preserved source, and both dependencies now
compile. Its absence from `lean/` does not withdraw the mathematical obligation.
The existing node signature and proof plan agree with the archived proof, so no
node edits or statement correction are needed. The only archived direct caller
still uses the theorem with exactly these local witnesses. No open return entry
for this item was present in `coord/returns/F1.md`.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
