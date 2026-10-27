## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.RationalP1.second_pretrace` by an explicit
assembly of two independent forward coherence identities. Proved private categorical lemmas
cancel the forward square using exactly hq, hx, hb and hp. The record assembly is checked with
abstract coefficient and object variables before substituting the actual rational coefficient.
This keeps the native exchange comparisons folded and avoids expensive normalization on the
concrete twisted object. The assembly cancels the canonical tensorShiftIso pair and identifies
the result with the original unitTail and counitProjectionPart, preserving the full statement
and all its binders.

The two intermediate modules are `RationalP1SecondExchangeProjection` and
`RationalP1SecondProjectionInterchange`. The first is the forward exchange/tensor square with
inside T and outside K, with no twisted projection and no invertibility hypotheses. The second
uses an arbitrary scalar arrow z and forward p2 projections, with no exchange map, tail,
counit, or inverse projection. Neither is the original pretrace equation under a new name:
their common boundary is the explicit forward map `secondExtractProjection`, and the Lean
assembly substitutes one square into the other before inverting the composite.

Moved the existing helper definitions and equation interface, with their signatures, attributes
and bodies unchanged, into `RationalP1SecondPretraceData`, reexported publicly by the original
item. This makes the lower modules importable without a cycle. The data module also constructs
`secondExtractProjection` as a literal forward composite. The explicit
`secondPretraceExchangeMap` wrapper also keeps the native exchange through fixed functor
endpoints, without altering its value. Its `secondPretraceExchangeMap_isIso` and
`secondPretraceExchangeMap_inverse` API lemmas are proved from the definitions. The change
record is `coord/changes/M3-rational-p1-pretrace-map-ownership.md`.

Edge checks of the new statements: zero K and zero z give zero maps on both sides; empty Y
gives the unique maps in the zero category; the local rank-one calculation uses the even shift
two and therefore has sign (-1)^4=1. No finiteness, constructibility or boundedness assumption
is introduced. The unit route is the same extraction of q*K followed by the two-factor
projection calculation.

Validation: all four delivered Lean modules and four existing consumers compiled
cleanly, with no warnings. The item took 33.1 seconds; the data module 41.0;
the two forward modules 24.3 and 35.7. The direct consumers
`RationalP1ScalarChernMaps` and `RationalP1SecondScalarTrace` took 47.6 and 40.7;
`RationalP1SecondTraceReordering` took 27.5. A newer snapshot of
`RationalP1ScalarChernBaseChange` was refreshed and compiled separately in 12.9
seconds, including its two unpublished dependencies. The consumer copies were
removed after validation; none is changed or delivered. The original theorem
signature and moved declaration bodies were checked verbatim. The final DAG has
no cycle through a delivered node.

## Proved and sorry left

This is a decomposition, not a completed proof of the geometric coherence.

Closed the original local hole in `AlgebraicGeometry.ProEtale.RationalP1.second_pretrace` (node
`lem-sfb-rational-p1-second-pretrace`) by a complete Lean proof from the two forward
statements. The private `transport_forward`, `inverse_square`, `assemble_pretrace` and
`generic_record_assembly` helpers are fully proved.

Added exactly two named public theorem holes, each the entire proof `by sorry`:

- `AlgebraicGeometry.ProEtale.RationalP1.second_exchange_projection`, node
  `lem-sfb-rational-p1-second-exchange-projection`.
- `AlgebraicGeometry.ProEtale.RationalP1.second_projection_interchange`, node
  `lem-sfb-rational-p1-second-projection-interchange`.

The item has zero remaining local holes; the new modules have two in total. Holes closed: one.
Holes added: two. This packet has net minus one closed hole and prunes no module. Every
definition is a real construction with no sorry. The two forward geometric normalizations
remain for further proof work.

## No longer needed

No node or module is pruned. The item's direct public imports of
`RationalP1SecondPullComparison` and `RationalP1AmbientTail` move to the data module and remain
public transitive dependencies. All three original substantive tools (ringed exchange/tensor
coherence, module/ringed comparison, and two-factor projection coherence) remain needed by the
new nodes. They are not imported into the assembly merely to expand its dependency closure; the
relevant lower proofs will import them where used.

## Where the brief, the DAG or earlier work was wrong

The current queue records a proof item with one hole. Its archived build-error file reports
failed imports of SecondPullComparison and AmbientTail. The untouched item compiled against the
current published artifacts, so that archived import failure was not reproduced; this delivery
changes the proof rather than claiming a rebase repairs that failure.

The stated generic ringed laws are available and were read, including the module comparison's
tensor, adjunction, projection and composition signatures. They do not directly elaborate as
equations of these fixed projective-line module maps: the normalization through tensorShiftIso
and the pulled line comparisons is a separate mathematical step. The two new nodes expose those
precise forward normalizations and retain the original tool dependencies. The assembly itself
now checks their source and target matching and all inverse cancellations.

A dependency traversal also encountered the pre-existing cycle
`lem-pc-ring-hom-extension-differential` → `lem-pc-ring-hom-extension-differential-adjacent` →
`lem-pc-ring-hom-extension-differential`. Neither node is changed here. No cycle passes through
a delivered node; the unrelated cycle is reported for maintainer review.

## New nodes

`def-sfb-rational-p1-second-pretrace-data` records the unchanged helper maps moved out of the
item and the added forward extraction projection and exchange wrapper. Its data are explicit
composites and its module has no proof holes.

`lem-sfb-rational-p1-second-exchange-projection` is the forward exchange square with inside T
and outside K, before introducing the outside Tate factor. It has no hypotheses asserting
invertibility.

`lem-sfb-rational-p1-second-projection-interchange` is the independent forward two-factor
projection calculation for arbitrary V and arbitrary scalar arrow z. It includes the even Tate
self-interchange normalization and contains no exchange.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.RationalP1SecondExchangeProjection": "2e9428f85207001c26b285a862a098a716963e58", "Sheaf.Paper.RationalP1SecondPretrace": "c2619b530724f0ccbe373a2265c00f84f7f1d1d4", "Sheaf.Paper.RationalP1SecondPretraceData": "b70f903aed2e00469015b9d0b44fafb240e1f14f", "Sheaf.Paper.RationalP1SecondProjectionInterchange": "19ef39bf3d6eb67179e17feaa0d225adbf01bd6e"}, "results": {"Sheaf.Paper.RationalP1ScalarChernMaps": {"hash": "85a0d646ca997eb835d2a2d1cdbdbd68a92baaf5", "status": "OK"}, "Sheaf.Paper.RationalP1SecondScalarTrace": {"hash": "70acd7b00b358a93fcf8c88dc8ac321dc76dfd70", "status": "OK"}}, "seconds": 203, "time": "2026-10-28T04:12:27+0800", "transitive": 0, "version": 1}
```

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
