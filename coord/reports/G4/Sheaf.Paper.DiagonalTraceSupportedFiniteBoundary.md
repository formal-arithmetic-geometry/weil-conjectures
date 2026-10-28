## What changed

Repaired all three objections in reviewer C-a12ff's return of head a12ff12f8ca.
The old source witness and false target implication have been replaced. The
item's statement and its original public imports are unchanged.

The proof now follows the node's three stages. Source projection produces a
normalized finite coefficient frame and identifies the supported composite with
the fixed residue Cartier class. Cartier reduction and supported Kummer Chern
realization are supplied by the existing proved
`cartier_reduction_site_comparison`; a proved specialization extracts its
geometric Chern clause. A separate coefficient comparison takes any finite
Cartier class satisfying that geometric equation and compares it with the
normalized Chern arrow.

The large source equation is named by an explicit definition so its category
interfaces are checked once, rather than repeatedly unfolded in the theorem.

The source step assumes and uses `hxi`, `hs`, `he` and `hp`. The coefficient
comparison assumes and uses `hn` and `hc`, and has no `D`, `H`, `xi`, `s`, `p` or
supported-source composite. Thus neither remaining step restates the item.
The parent proof combines their equations using the proved typed assembly
lemma, which transports the boundary equation along its endpoint equality.

The frame coordinates are ordinary sheaf isomorphisms normalized on local one
and on the actual root tensor map. Its Cartier map is explicitly constructed
from the actual coefficient projection, the constant-to-supported unit and the
specified finite Cartier class. No definition chooses data from an unproved
existence statement. The existential frame is used only inside the theorem
proof. The auxiliary modules are imported privately by the parent.

All new node records have full statements, statement dependencies, proofs in
words, current searches, exact Lean signatures and group G4.

Validation: import-order compilation and individual follow-up compiles checked
the supporting modules. The expanded parent proof had unstable checking time,
so its self-contained equation assembly is now a proved typed API lemma in a
separate module. Profiling options have been removed. The delivery command runs
the compiler and complete preflight checks on the final packet. The typed
assembly module checked in 37.3 seconds and the parent, without profiling
options, checked in 49.3 seconds. All seven modules have been checked.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_supportedFiniteBoundary`
is closed by a complete proof from two strictly smaller statements. This is a
decomposition, not a net proof-count improvement: one original hole is closed
and two lower holes are added.

`diagonalTrace_supportedFiniteBoundary_cartierKummer` is proved from
`cartier_reduction_site_comparison`, with no new hole.
`diagonalTrace_supportedFiniteBoundary_combine` is proved by endpoint transport.
All coordinate and
Cartier-map definitions are explicit constructions.

Exactly two `sorry`s remain in this delivery, both complete named theorem bodies:

- `diagonalTrace_supportedFiniteBoundary_sourceStep`, node
  `lem-sfb-diagonal-trace-supported-finite-boundary-source-step`;
- `diagonalTrace_supportedFiniteBoundary_targetStep`, node
  `lem-sfb-diagonal-trace-supported-finite-boundary-target-step`.

The item's own module has zero `sorry`. No definition contains a hole.

## No longer needed

Removed redundant FiniteCartierNormalization imports from the new Maps and
Equation modules; the source theorem imports that normalization directly.
No existing library module or node is withdrawn or pruned. All three original
geometric proof stages remain in the dependency route. The middle stage needs
no new unproved theorem: its statement is already a proved clause of
`cartier_reduction_site_comparison`.

Discarded from the returned, never-landed packet:
`SupportedFiniteBoundarySourceEquation`, `supportedFiniteBoundaryRootMap`,
`supportedFiniteBoundaryChernMap`, the arbitrary source-witness split and the
old categorical combination wrapper. Its module now contains the proved typed
assembly lemma for the fixed Cartier and Chern equations. The old source-equation,
root-map and codomain-map node proposals are replaced by the actual finite-frame
and Cartier-map records; the combination node is rewritten to match its new API.
These proposals were absent from current main, so no published DAG node or Lean module is
deleted. No adopted source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The review is correct. The previous target step had dropped every hypothesis
that related the strict class to a Cartier/Chern class; with a zero presented
arrow it falsely forced every Chern composite to vanish. Adding the hypotheses
back would only move the original obligation. The previous source step was the
tautology that a composite equals some map. Neither was a genuine reduction.

This repair fixes a canonical intermediate finite Cartier class and normalized
coordinates, separates its source projection from its coefficient Chern
comparison, and proves the geometric middle step using an existing theorem.
The mathematical edge checks cover n=0 (positive exponent one), the empty
scheme (unique maps), and a zero presented arrow: the latter is constrained by `hp` and `hxi`,
so there is no unconditional vanishing assertion. The original node plan and
unit route are retained. The previous G3 attribution was erroneous; the new
records correctly attribute this work to G4.

## New nodes

`def-sfb-diagonal-trace-supported-finite-boundary-frame`: normalized finite
coefficient and Tate-line isomorphisms, fixed on one and roots.

`def-sfb-diagonal-trace-supported-finite-boundary-unit-coordinates`: the exact
single/evaluation coordinate comparison, constructed from canonical isomorphisms.

`def-sfb-diagonal-trace-supported-finite-boundary-line-coordinates`: the shifted
version, including both exact shift comparisons.

`def-sfb-diagonal-trace-supported-finite-boundary-cartier-map`: the explicitly
constructed coefficient-projected finite forget-support Cartier arrow.

`def-sfb-diagonal-trace-supported-finite-boundary-cartier-equation`: the fixed
Cartier endpoint equation, named to share categorical structures in kernel checks.

`lem-sfb-diagonal-trace-supported-finite-boundary-source-step`: the source
projection, using the finite-cycle, cone, root and presentation normalizations.
This is the first remaining hole.

`lem-sfb-diagonal-trace-supported-finite-boundary-cartier-kummer`: the geometric
Chern equation for the residue Cartier class, proved by specializing the existing
site comparison theorem.

`lem-sfb-diagonal-trace-supported-finite-boundary-target-step`: coefficient Chern
comparison for any geometrically normalized finite Cartier class, using
FiniteChernNormalization and the scalar-unit Ext bijection. This is the second
remaining hole.

`lem-sfb-diagonal-trace-supported-finite-boundary-combination`: a proved equation
assembly lemma. It transports the fixed Cartier endpoint to the Chern endpoint;
it has no new mathematical hypotheses or holes and keeps their interfaces cached.

The statements and proofs follow paragraph (2) of the diagonal trace proof.
LeanSearch and LeanFinder found no direct Mathlib geometric comparison; Loogle
and grep located the exact-functor APIs and the existing project middle clause.
No change to an existing shared signature or definition is made, so no consumer
adaptation or definition change record is required.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.DiagonalTraceSupportedFiniteBoundary": "f1e7c3be19cf4ecf6c4ed463362cffee9ff8c366", "Sheaf.Paper.DiagonalTraceSupportedFiniteBoundaryCombine": "74b485ec39128e38bc58634e586dc39e089fc583", "Sheaf.Paper.DiagonalTraceSupportedFiniteBoundaryEquation": "6b910feaff8f76256dbb3c9fe804b01871d73ae4", "Sheaf.Paper.DiagonalTraceSupportedFiniteBoundaryMaps": "0763ba74ff8b3b19a95bee027a65eee191a41ad3", "Sheaf.Paper.DiagonalTraceSupportedFiniteBoundaryNormalization": "9526c9299359b0d3569a2dd25c83fb7c3e7b0258", "Sheaf.Paper.DiagonalTraceSupportedFiniteBoundarySource": "4afd3b276f0428039496ca53b143d041c680311e", "Sheaf.Paper.DiagonalTraceSupportedFiniteBoundaryTarget": "92c27969eac65b2c73e3697b1423a7aea2ac816c"}, "results": {}, "time": "2026-10-28T10:55:56+0800", "transitive": 0, "version": 1}
```

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
