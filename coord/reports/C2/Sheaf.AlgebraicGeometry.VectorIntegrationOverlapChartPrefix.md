## What changed

The original theorem `AlgebraicGeometry.Etale.vectorIntegration_overlap_chart_prefix`
is reduced to two strictly separate parts of its argument. Its statement, three public
prefix definitions and existing public import are unchanged. The two new imports used
by the proof are private proof imports.

`VectorIntegrationCartesianPrefix` constructs the direct descended-coefficient prefix
for an arbitrary Cartesian affine chart. Its action theorem is proved, without a new
hole, from existing exchange pasting and source inverse-image associativity/unit laws.
The proof explicitly establishes coefficient composition, specializes horizontal
exchange pasting to an automorphism over the identity, uses naturality, and cancels
comparison isomorphisms. The construction allows an arbitrary base object L and its
specified comparison b; it has no frames or open restrictions. The same module defines
the geometric restricted chart and proves its Cartesian-square property by pasting.

`VectorIntegrationOverlapCoordinates` states only the geometric linear-coordinate
relation between the two restricted inverse frames. It has no coefficient ring or
exchange morphisms. `VectorIntegrationRestrictedChartTransport` states only the
comparison between restriction of one frame's prefix and the direct composite-square
prefix. It has no second frame, change-of-frame matrix or affine action. Their complete
proofs in words and DAG nodes follow the geometric and transport parts of the original
plan. The item applies the restriction comparison twice and the proved Cartesian-prefix
action theorem once.

Validation: `lcompile.py --all` compiled all four delivered modules cleanly: the
Cartesian-prefix module in 36.4 s, coordinate module in 29.6 s, single-chart transport
module in 31.3 s and original item in 36.5 s. The original theorem signature and all
three prefix definitions are unchanged, and all node Lean statements match their
modules verbatim. The sibling import graph is acyclic; no new DAG dependency returns
to the item.

The empty-open, rank-zero and zero-coefficient cases have been checked against the
formulas: restriction and compositor laws are still defined, empty matrices are
invertible, and there is no nonempty/positive-rank/nonzero-ring hypothesis. No choice
of data from an unfinished existence theorem is introduced.

## Proved and sorry left

One original hole is closed by a complete combining proof:
`AlgebraicGeometry.Etale.vectorIntegration_overlap_chart_prefix`, node
`lem-amb-vector-integration-overlap-chart-prefix`. There are zero holes left in the
item module.

The following new results are proved without adding a hole:
`AlgebraicGeometry.Etale.vectorIntegrationCartesianPrefix_action` and
`AlgebraicGeometry.Etale.vectorIntegrationRestrictedChart_isPullback`, together with
the private coefficient-composition and named-pasting lemmas. Their node is
`lem-amb-vector-integration-cartesian-prefix-action`.

Two holes are added, each the entire body of a public theorem in its own module:

- `AlgebraicGeometry.Etale.vectorIntegration_overlap_coordinates`, node
  `lem-amb-vector-integration-overlap-coordinates`.
- `AlgebraicGeometry.Etale.vectorIntegration_restricted_chart_transport`, node
  `lem-amb-vector-integration-restricted-chart-transport`.

This is a decomposition of the original obligation, not a complete proof of it:
one original hole closed, two simpler holes added, net minus one before any
independent progress on dependencies. Neither split is the original conclusion with
a renamed or repackaged hypothesis. The categorical action calculation is proved here,
not delegated to either split.

## No longer needed

No existing import, module or mathematical dependency is globally pruned. The redundant
direct proof import of `UpperStarCompCoherence` in the new Cartesian-prefix module was
omitted: exchange coherence already publicly reexports its associativity API. The original
public chart import stays. The item's direct proof dependencies now refer to the two
smaller comparison statements and the proved Cartesian-prefix action theorem.
Original dependencies on exchange coherence, finite-coefficient compact supports,
normalized finite Tate transport and the affine tower remain used below these results;
the direct-dependency rewrite does not claim that their modules can be withdrawn.
No projective-line datum, counit, descent or affine linear trace-invariance theorem is
needed in the new prefix-action calculation.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original plan combines a geometric
transition calculation with a single-chart restriction comparison and an exchange
calculation. Those components were not separate usable declarations. The new geometry
and restriction nodes state the first two precisely; the categorical calculation is
now written in Lean from the existing public exchange/coherence declarations.

The original coordinate convention is preserved: if e'_j = sum_i G_ij e_i,
then the inverse chart relation uses inverse(G transpose). None of the new statements
assumes that the common open is affine.

## New nodes

`lem-amb-vector-integration-cartesian-prefix-action` records the direct Cartesian-prefix
construction, its proved automorphism action equation, and the restricted geometric
chart with its proved Cartesian property. It uses exchange pasting and canonical
inverse-image composition/unit laws. It is coefficient descent for an arbitrary L
and b, independent of frame transitions.

`lem-amb-vector-integration-overlap-coordinates` isolates the coefficient-free scheme-map
relation from original proof Steps 1--2. Its proof restricts the two module frames,
forms mutually inverse global matrices, and checks degree-one generators.

`lem-amb-vector-integration-restricted-chart-transport` isolates the one-frame
restriction comparison from original Steps 3--4. Its proof pastes the two squares,
transports the bounded/unbounded comparisons, and inducts on the ordered Tate tensor
for coefficient coherence.

No existing interface was changed, so there is no change record or forced adaptation.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
