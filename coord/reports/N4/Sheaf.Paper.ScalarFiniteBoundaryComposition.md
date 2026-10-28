## What changed

Replaced the sole hole in `scalarFiniteBoundary_boundaryEquality` by the actual
scalar-adjunction, exact-evaluation and endpoint calculation. Both original theorem statements are unchanged.

The scalar-model calculation first extends the supplied unit formula from
K-flat representatives to arbitrary complexes using a K-flat resolution and
naturality. It also identifies the supplied adjunction with its canonical
counterpart, so the supplied scalar shift is compatible with that adjunction.
The root transpose therefore works without assuming that the root module is
flat. Unit naturality and the source normalization give the scalar arrow formula.

Exact single-arrow transport laws apply this formula through the recorded
forgetting and finite evaluation. Constructed an explicit natural isomorphism
between that functor and finite scalar evaluation followed by forgetting. Its
components are identity transports on actual sections; no arbitrary existence
witness or data hole is used. The integer-cast equation identifies the source
map with `finiteQuotient`. The ordinary scalar unit and the pure-tensor equation
of `lineEvaluation` identify the root map with `finiteRootMap`. A categorical
square calculation then proves the original finite-boundary equality.

The two existing endpoint definitions were extracted verbatim to
`ScalarFiniteBoundaryArrows`, publicly reexported by the item. Their names,
visibility, binders, formulas and meaning are unchanged. After optimizing the
concrete calculation using proved generic transport laws, profiling still found
81 seconds in the combined proof module. The existing composition theorem now
lives in `ScalarFiniteBoundarySquare` and proves the equation directly. The
existing witness theorem in `ScalarFiniteBoundaryEquality` packages that equation.
The item publicly reexports this chain. This separates kernel checking of the
large derived-arrow types without changing either signature. The remaining new
modules contain the proved calculations just described. Proof imports are
private. No existing source-library file is modified.

The proof follows clause (2) of the current geometric-classes blueprint and the
finite-evaluation step of `det-prop-diagonal-tower-trace`. It uses the already
proved K-flat resolution and exact-derived single comparison APIs; these are
needed tools for the same route, not replacements for a unit's own argument.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.SpTowerClasses.scalarFiniteBoundary_boundaryEquality`
(`lem-sfb-scalar-finite-boundary-composition-endpoints`). The composition theorem is proved directly by the scalar transpose and endpoint
calculation; the boundary-equality theorem packages its equation.

Added holes: zero. Remaining holes in the item and every new module: zero.
The final dependency-chain compile passed: generic exact transport 12.5 seconds,
direct square 58.5 seconds, witness packaging 16.2 seconds, public item 5.4
seconds, and the unchanged direct importer 52.7 seconds. The unchanged consumer
copy was removed from the packet after this check.

No split-off unproved statement is introduced. Every public helper listed in
the new nodes below is proved or explicitly constructed.

The formulas were checked on the zero arrow and on empty/zero section groups:
the argument uses only naturality, equality transport and uniqueness equations.
It adds no nonzero coefficient, nonempty scheme, flat root or Kummer-generation
hypothesis.

## No longer needed

No existing node or module is pruned. The original definition dependencies are
still used by the proof, directly or through its proved calculations. The item's
public import of `TowerScalarFiniteBoundaryData` is replaced by the public import
of `ScalarFiniteBoundaryEquality`, which publicly reexports
`ScalarFiniteBoundarySquare`, then `ScalarFiniteBoundaryArrows`, and the same
data module.
This preserves its public dependency surface.

The direct rewrites of the concrete derived-arrow definitions are replaced by
`scalarFiniteBoundary_eval_eq` and `scalarFiniteBoundary_integral_eq`. Their
underlying definitions and generic transport dependencies remain needed.

No trial diagnostic module or source-library adaptation is delivered. There are
no unused proof imports in the delivered modules.

The private generic extraction helper `finiteBoundaryEquality_comp` is no longer
needed: the actual equation is proved first and its HEq witnesses are then
reflexive. The two original theorem nodes are retained and their dependency
direction and Lean module attachments follow this proof.

## Where the brief, the DAG or earlier work was wrong

The original endpoint node's `source.document` records an obsolete flat path.
Its updated `proof_origin.document` and all new nodes cite the existing nested
file under the current `latest` blueprint. The original source field is retained
because route edits are limited to the prescribed proof and Lean fields.

No theorem statement was changed. The obligation can be closed instead of moved
to another endpoint-witness restatement. The essential target calculation is
valid for every root module; the model unit formula on an arbitrary complex
comes from a K-flat resolution, so root flatness is unnecessary.

A bare scratch import initially displayed an unrelated private-declaration
collision. A proper module-mode probe compiled against the published library;
the trial compatibility edit was discarded. This delivery includes no such
repair.

Whole-functor reflexivity for the evaluation comparison caused excessive
unfolding. Explicit natural isomorphisms with identity section components avoid
that unfolding and preserve the actual underlying sheaves. The definition
extraction and consumer check are documented in
`coord/changes/N4-scalar-finite-boundary-arrows.md` and
`coord/changes/N4-scalar-finite-boundary-equality-module.md`.

## New nodes

`def-sfb-finite-boundary-arrows`: the two unchanged endpoint definitions in
`ScalarFiniteBoundaryArrows`, moved from the item.

`lem-sfb-scalar-model-unit`: `ScalarData.unit_model` on arbitrary complexes in
`ScalarModelUnit`, proved using a K-flat resolution.

`lem-sfb-scalar-adjunction-unique`: `ScalarData.adjunction_eq` in the same module,
proved by equality of ordinary units and then derived units.

`lem-sfb-scalar-root-transpose`: `scalarRootTranspose` in `ScalarRootTranspose`,
proved by the model-unit formula and the ordinary single adjunct calculation.

`lem-sfb-normalized-scalar-arrow`: the general shift-compatible adjunction-unit
calculation in `NormalizedScalarArrow`.

`lem-sfb-scalar-arrow-transpose`: `scalarArrowTranspose` specializes the preceding
calculation with the supplied source normalization and the proved root transpose.

`lem-sfb-exact-arrow-transport`: the proved natural-isomorphism, composition,
precomposition, postcomposition, evaluated-arrow, underlying-arrow, square
gluing, exact assembly and endpoint identification laws in
`FiniteBoundaryExactTransport`.

`def-sfb-finite-underlying-evaluation`: explicit natural isomorphisms on the
underlying additive sheaves of scalar restriction and evaluation in
`FiniteBoundaryUnderlyingEvaluation`.

`def-sfb-finite-forget-comparison`: the constructed comparison isomorphism and
its proved section and morphism formulas in `FiniteBoundaryForgetComparison`.

`lem-sfb-finite-source-map`: the identification with `finiteQuotient` in
`FiniteBoundaryEndpointMaps`, proved by its unique integer-cast equation.

`lem-sfb-finite-root-map`: the identification with `finiteRootMap` in the same
module, proved by its unique pure-tensor equation.

Change records: `coord/changes/N4-scalar-finite-boundary-arrows.md` and
`coord/changes/N4-scalar-finite-boundary-equality-module.md`.

`lem-sfb-finite-boundary-arrow-formulas`: the two proved formulas in
`ScalarFiniteBoundaryArrowFormulas` specialize exact transport to the original
arrow definitions. The final assembly uses these formulas rather than unfolding
the derived functor constructions in the concrete coefficient categories.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteBoundaryEndpointMaps": "ebb02f1229f6df1f03a0391082444a807d36b685", "Sheaf.Paper.FiniteBoundaryExactTransport": "0bf018e541dff15d1f10c76e8349f3e50529b35b", "Sheaf.Paper.FiniteBoundaryForgetComparison": "35cc0333b658b8a62f4dc6bcb83d0916be9bbcc1", "Sheaf.Paper.FiniteBoundaryUnderlyingEvaluation": "91494af1c410439c39c1a9d21347ac641c6d7c67", "Sheaf.Paper.NormalizedScalarArrow": "c2008be45c5e86390c7e51fd2c34ef1f638805b3", "Sheaf.Paper.ScalarArrowTranspose": "c7082ad8598b91abe961869f03fd58bbe0678ed7", "Sheaf.Paper.ScalarFiniteBoundaryArrowFormulas": "0c79625f36e25f9520af32df92f1a63b483e6d33", "Sheaf.Paper.ScalarFiniteBoundaryArrows": "0efa5c147e8ff0bf0887073d533af7d3413f021a", "Sheaf.Paper.ScalarFiniteBoundaryComposition": "f4498623e80b22fe565394eb58d76ad2c6cb4be1", "Sheaf.Paper.ScalarFiniteBoundaryEquality": "689d853efe1f4f3f4bb8b749b57cb0dbe8b11f51", "Sheaf.Paper.ScalarFiniteBoundarySquare": "338bf2a9b659c8bf13388a716c64975283e6983d", "Sheaf.Paper.ScalarModelUnit": "81da56062c0dc8af9d35b32c86f409754c0be650", "Sheaf.Paper.ScalarRootTranspose": "cebe359f68c24af75dcb37d8b1f644007d42ebe1"}, "results": {"Sheaf.Paper.TowerScalarFiniteBoundary": {"hash": "aca96c6ab8d0c649810512019228408581265645", "status": "OK"}}, "seconds": 66, "time": "2026-10-28T11:31:41+0800", "transitive": 0, "version": 1}
```

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
