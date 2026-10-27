## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Monoscheme.exists_unique_centeredToricTowerLift` with a compiling
combination of the construction theorem and the centered-identification theorem, followed
by the existing rational toric regularity theorem. The terminal smoothness implication
transports local Noetherianity across the supplied scheme isomorphism and regularity across
its stalk ring isomorphisms, then applies
`isSmooth_of_rational_realization_regular` using the lift's torsion-freeness field.

Extracted the three existing data declarations into
`Sheaf.AlgebraicGeometry.CenteredToricTowerLiftData` to avoid an import cycle with the two
new proof modules. Their names, signatures, fields, bodies and visibility are unchanged;
the item reexports them by a public import. Its four original public imports and its
original theorem signature are unchanged. There are no source-library changes or adapted
existing modules. The extraction is recorded in
`coord/changes/R5-centered-toric-tower-data-extraction.md`.

The first compilation of all four files succeeded in 6.4, 5.5, 5.8 and 5.5 seconds per
file. It reported two `haveI` style warnings in the main proof; replacing those commands
with `have` gave a clean 3.3-second recompile. No profiling options, nonstandard axioms,
or holes in definitions were added. The delivery tool performs its own probes and checks.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.Monoscheme.exists_unique_centeredToricTowerLift`
(node `lem-trf-monoscheme-toric-tower-descent`) by decomposition. Its final smoothness
implication is fully written from the existing rational regularity declaration.

Added exactly two holes, each the whole proof of a public theorem in its own new module:

- `AlgebraicGeometry.Monoscheme.exists_centeredToricTowerLift`, node
  `lem-trf-centered-toric-tower-lift-existence`, is construction only (original steps 1--3).
  It asserts neither uniqueness nor terminal smoothness.
- `AlgebraicGeometry.Monoscheme.existsUnique_centeredToricTowerIdentification`, node
  `lem-trf-centered-toric-tower-lift-identification`, compares two supplied lifts
  (original step 4). It assumes those lifts and does not construct a lift of an input tower
  or assert smoothness. The external equivariance and nowhere-density hypotheses are
  unnecessary once the lifts are supplied.

Thus the item has zero remaining direct holes; the new modules have two. This is one
upper hole closed and two strictly partial lower obligations added, a decomposition with
net hole count minus one, not a completed axiom-free proof or positive net proof progress.
The data module has zero holes. Existing dependency holes are unchanged.

## No longer needed

None. No mathematical dependency, module, node or original public import is pruned.
The original construction steps are retained in the existence node; the original
uniqueness step is retained in the identification node; the smoothness step still uses
`lem-trf-toric-monoid-comparison`. The original direct finite-component proof dependency
moves into the construction and identification nodes and remains needed there.

The three data declarations move out of the original node's `lean.declarations` into
the new definition node; their implementation is moved, not copied or withdrawn. No
existing downstream consumer imports the item yet, but its DAG parents remain in place.
No withdrawal is proposed.

## Where the brief, the DAG or earlier work was wrong

The declaration is retained unchanged and is not disputed. The plan's uniqueness step
was marked elementary, but its stated dependencies do not directly provide the required
global monoscheme isomorphisms: it needs the saturated chart maps, their agreement on
localized overlaps, and faithfulness of monomial realization. Likewise the one-step
blowup comparison does not by itself implement the finite centered induction or the
transport of the original component torus actions. These are the two exposed obligations.

Read ILO VIII 3.2.14--3.2.20, printed pp.105--106, directly from the local PDF. Checked
length zero, empty monoschemes, multiple components, unit centers and unsaturated initial
monoids. Unit-center normalization stages are retained. The construction does not require
a regular final scheme; the identification theorem compares already supplied lifts and
uses their torsion-freeness fields. The existing unit and chapter route are unchanged.

LeanFinder and LeanSearch returned ordinary scheme normalization and descent-map facts;
Loogle returned no match for the regular-scheme isomorphism query; Mathlib grep found no
monoscheme/toric-blowup fact. Searches of the project found the data already in this item
and no theorem implementing these two remaining steps. Blueprint searches for centered
toric tower, saturated blowup tower and unique monoid returned no matching blueprint node.
Every new node records the actual logged searches.

## New nodes

`def-trf-centered-toric-tower-lift-data` records the three existing data declarations now
in `Sheaf.AlgebraicGeometry.CenteredToricTowerLiftData`. It introduces no new mathematical
notion or existence claim; it extracts their ownership from the original theorem node.

`lem-trf-centered-toric-tower-lift-existence` states the construction portion of ILO VIII
3.2.19. Its source and full inductive proof are in both the node and declaration docstring.

`lem-trf-centered-toric-tower-lift-identification` states the canonical comparison portion
of ILO VIII 3.2.20 for two already supplied lifts. Its source and full chartwise uniqueness
argument are in both the node and declaration docstring.

Change record: `coord/changes/R5-centered-toric-tower-data-extraction.md`.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
