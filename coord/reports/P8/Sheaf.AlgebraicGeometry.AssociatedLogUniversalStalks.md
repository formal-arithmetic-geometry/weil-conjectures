## What changed

Reduced `AlgebraicGeometry.associatedLog_universal_stalks` without changing its
statement. The proof constructs the presentation from `prelog_pushout_log_axiom`,
identifies its arbitrary quotient with the prescribed quotient by a componentwise
bijection, proves the global universal mapping property using
`prelog_pushout_hom_extension` and terminal-object naturality, and obtains the
étale restriction comparison from `etaleLogPresentation_restriction`.

The final chart consequence uses the compatible-range assertion to construct the
log map. After its isomorphism is recognized, the Lean proof explicitly transports
injectivity and the exact compatible range along the isomorphism and its inverse.

The original definitions and three already proved quotient-restriction lemmas
move verbatim to `Sheaf.AlgebraicGeometry.AssociatedLogPresentation`, publicly
re-exported from the original module. This permits the two separate intermediate
modules to depend on the presentation without an import cycle. Their definition
node follows the new location. See
`coord/changes/P8-associated-log-presentation-extraction.md`.

Validation: all four delivered modules and all 20 current direct importers compiled
with `lcompile.py --all`, with no errors or warnings. The main module took 24.3 s;
the slowest importer took 29.1 s. Temporary unchanged consumer copies were removed
before submission. The main signature and all moved declarations were checked
byte-for-byte against the original.

Repair of returned head `31c1b3bc3`: the mathematical review passed; the
landing rejected a reviewer override named
`P8-associated-log-presentation-extraction.md`. The landing tool maps this
record to the override basename
`P8-associated-log-presentation-extraction.change.md` (see
`tools/batch_land.py`, `fixes`). The actual delivered record remains at
`coord/changes/P8-associated-log-presentation-extraction.md`; it is included
directly, so no reviewer override is needed for the record. This repair expands
its Old section to the complete verbatim block of all 16 relocated declarations
and refreshes the consumer holders against the current source. No mathematical
correction was specified in the return. The retained Lean and node edits were
compared with the current source; no intervening interface change needs merging.
The server compile checks passed again for all four delivered modules and all
20 current direct importers, without errors or warnings. The unchanged consumer
copies were removed after verification. The delivery tool rebuilds the packet
on current `sheaf-dag`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.associatedLog_universal_stalks`
(`lem-trf-associated-log-universal-stalks`). Its complete Lean proof now depends
on two new, strictly smaller intermediate statements. This is a decomposition,
not a complete proof of associated-log existence and all its comparisons:
1 original hole closed, 2 holes added, net -1. The item itself has zero holes.
The extracted definition module has zero holes, and the three restriction lemmas
keep their original complete proofs.

The two remaining holes are:

- `AlgebraicGeometry.associatedLog_presentation_stalk_comparison`
  (`lem-trf-associated-log-presentation-stalk-comparison`), in
  `Sheaf.AlgebraicGeometry.AssociatedLogStalkComparison`: for a *given*
  presentation, normalize the geometric-stalk pushout and its canonical chart.
- `AlgebraicGeometry.EtaleLogStructure.isIso_of_globalChart`
  (`lem-trf-log-map-global-chart-isomorphism`), in
  `Sheaf.AlgebraicGeometry.LogGlobalChartIsomorphism`: a *given* structural log
  map identifying two *given* charts is an isomorphism. It asserts neither
  existence of a presentation nor existence of a log map nor any universal
  mapping or restriction property.

Each is a public named theorem with its own module, node, source and full proof
in words. No definition has a hole or chooses an arbitrary witness from an
unproved existence assertion. The constructed log structure uses the specified
sheafification and structural map; only its log-axiom proof fields come from the
generic existence theorem.

## No longer needed

The main proof now directly needs only the generic prelog construction,
Hom-extension and étale-restriction theorems, plus the two new intermediate nodes.
Its two original public imports remain, and the extracted definition module is
added as a public import. No existing module is withdrawn.

The old direct dependencies `def-weil-pbc-geometric-stalks`,
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`,
`lem-trf-filtered-ring-log-pushout`,
`lem-trf-commutative-monoid-sheafification`, and
`lem-weil-pbc-sets-sheafification-geometric-stalk` are needed inside the new stalk
step and are recorded there rather than as direct steps of the main proof.
`def-trf-fs-log-blowup` remains a statement/definition dependency and is also used
by the new chart recognition node.

`lem-weil-pbc-colimit-constant-connected-diagram` is unnecessary on this route:
`filteredRing_logPushout` keeps the monoid fixed throughout, so a separate
identification of the constant monoid presheaf's stalk is not needed. No Lean
module is claimed globally unreachable merely from this dependency removal.

## Where the brief, the DAG or earlier work was wrong

The existing Lean statement and quotient construction needed no mathematical
repair. The current DAG's generic dependencies supply construction, extension and
étale comparison, as intended. The original module docstring still described the
older ten-step plan, while the current node has four grouped steps; the proof and
node now record the actual specialization and two remaining bridges.

The generic filtered-ring theorem works on a small filtered diagram, whereas the
geometric stalk is the colimit over the large pointed-neighbourhood category.
Its small final-model transport and sheafification normalization are the first
remaining bridge. The generic `etaleLogPresentation_comparison` tests charts on
the colimit of a prelog monoid presheaf; applying it directly to global charts
requires another constant-presheaf and unit-map normalization. The second
remaining lemma states precisely the stalkwise recognition needed here and gives
the direct proof in words. Neither remaining statement repackages the whole item.

Edge cases were checked in words: arbitrary nonintegral monoids, noninjective
beta, beta landing in units, the trivial monoid, zero section rings and the empty
scheme. Stalk pushout relations, rather than cancellation, govern the argument;
empty étale objects are covered by the sheaf axiom.

## New nodes

`lem-trf-associated-log-presentation-stalk-comparison` records original proof
steps 6--8 and the resulting canonical stalk chart. It imports the existing
filtered-ring pushout and monoid-sheafification modules and uses their exact
normalizations. Its file is
`lean/Sheaf/AlgebraicGeometry/AssociatedLogStalkComparison.lean`.

`lem-trf-log-map-global-chart-isomorphism` records only the stalk-conservativity
argument in original step 10. Its file is
`lean/Sheaf/AlgebraicGeometry/LogGlobalChartIsomorphism.lean`.

There is no new definition node: the existing
`def-per-associated-log-presentation` follows the verbatim declarations into
`lean/Sheaf/AlgebraicGeometry/AssociatedLogPresentation.lean`.
The change record is
`coord/changes/P8-associated-log-presentation-extraction.md`.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
