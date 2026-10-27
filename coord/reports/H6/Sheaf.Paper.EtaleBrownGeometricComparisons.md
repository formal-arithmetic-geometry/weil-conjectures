## What changed

Replaced the hole in `AlgebraicGeometry.etaleBrownGeometricComparisons` with a complete
combining proof from three strictly smaller comparison statements. Existing public
signatures, structures, definition bodies, and original imports are unchanged. The
three new imports are private proof imports. Proved private helpers express
inverse-square cancellation, pasting through a natural evaluation comparison, and the
canonical proper mate hom equation. The mate is locally irreducible after that equation
so downstream checks do not repeatedly unfold its joint-detection construction. This
local attribute changes no exported interface or definition body.

The proof constructs `levelComparison` and `projection` by the prescribed open/proper
composites. The proper singleton evaluation identity makes the evaluated canonical
mate invertible by cancellation; the existing above-level vanishing and joint detection
then construct its actual isomorphism on strict derived systems. Cancelling its hom
produces the inverse-mate evaluation square. Naturality of `directEvaluation`, followed
by the open singleton identity, proves the required `leftExtension_below` square.
In particular the final compatibility is proved by an equality of constructed maps,
without any assumption that derived evaluation is faithful.

The remaining finite-level normalization and the two singleton identities are stated
in separate modules, with source-specific proof docstrings and DAG nodes. They do not
assert `StrictEtaleBrownGeometry` or a repackaged equivalent: the finite-level statement
has no singleton data, while the singleton identities are each single equalities for
arbitrary fixed scalar comparisons and require no finite-field hypotheses.

## Proved and sorry left

Original holes: 1. Closed in the item module:
`AlgebraicGeometry.etaleBrownGeometricComparisons`
(node `lem-pur-etale-brown-geometric-comparisons`). No sorry remains in that module.

Added holes: 3, each the entire proof of its named public theorem:

- `AlgebraicGeometry.etaleBrownLevelComparisons`,
  node `lem-pur-etale-brown-level-comparisons`.
- `AlgebraicGeometry.etaleBrownProperSingletonEvaluation`,
  node `lem-pur-etale-brown-proper-singleton-evaluation`.
- `AlgebraicGeometry.etaleBrownOpenSingletonEvaluation`,
  node `lem-pur-etale-brown-open-singleton-evaluation`.

This is a decomposition, not a net proof gain: one upper hole is replaced by three
strictly smaller obligations (net holes closed minus added: -2). The existing
above-level and joint-detection helpers remain proved. No definition contains sorry,
and no data definition chooses a witness from any unproved existence theorem.
All existential witnesses are eliminated only inside the proof of the proposition.

Validation: all three new modules compile individually through lcompile.py. The final
item module compiles without warnings in 37.3 seconds, below the 60-second limit.
All Lean lines are at most 100 characters; the item module has no remaining sorry.

Edge cases checked against the statements and the proof: `m = n` uses the actual
identity coefficient transition; `n = 0` is the positive exponent one; `t` a unit gives
the zero quotient ring and zero module categories; `t = 0` gives constant coefficients.
Neither singleton identity divides by `t`, excludes the zero ring, or assumes
regularity, completeness, flat coefficient transitions, or bounded complexes.

## No longer needed

No module is withdrawn or pruned and no original import is removed. The finite-level
proof does not need `lem-pur-etale-system-coefficient-projection` or its successive
coefficient cocycle: its proper tensor-unit and open scalar-unit calculations suffice.
The original node retains its statement citation for the name compactScalarMap.
Constant-ring module sheaves, exact derived factorization and mate pasting are carried
by the new nodes. No upstream declaration is removed or replaced by a hole. The unit
`sk-def-sf-operations` and its route are kept.

## Where the brief, the DAG or earlier work was wrong

The cited general coefficient projection theorem concerns its own normalized system
presentation. It does not directly supply the comparisons for an arbitrary fixed
`StrictEtaleCompactSupport S`, including its realization/unit/mate equations. Likewise,
`systemSingleDerivedTranspose` is stated for its constructed general system model,
whereas this item accepts an arbitrary recorded coefficient-evaluation package.
Comparing those normalized presentations is required; this delivery does not treat
their existence as giving unspecified freely chosen isomorphisms.

Preflight exposed a broad DAG dependency cycle through the general system projection
coherence and integral reconstruction route. The finite-level node now uses the direct
proper tensor-unit and open scalar-exchange calculations instead. A narrow definition
node records the existing `Etale.SystemProjection.constantModule` declaration, which
is the only part of the general system projection data used by Brown realization.
The realization node's stmt_deps is corrected to cite that declaration, with no change
to its statement or any Lean interface. See the dependency-granularity change record.
A reachability check finds no cycle through any new node or the realization node.
The original item has a pre-existing cycle through its unchanged statement citation;
this packet adds no path from a new node back to the item.

The existing blueprint ancestry is broken at a module-name `created.item`:
`tools/blueprint_refs.py ancestor lem-pur-etale-brown-geometric-comparisons` reports
`None`. The new nodes record that same absence and explicitly identify the source
steps they serve. The current blueprint was read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-def-purity-conv/`
`det-def-sf-operations.md`; the older unit record still names a different path.

## New nodes

`lem-pur-etale-brown-level-comparisons` in
`lean/Sheaf/Paper/EtaleBrownLevelComparisons.lean`: the normalized finite-level
realizations, geometric images, scalar mates and their published compact-scalar
normalization. The composite level and scalar maps are explicit local expressions in
the statement; the main theorem constructs those expressions itself.

`lem-pur-etale-brown-proper-singleton-evaluation` in
`lean/Sheaf/Paper/EtaleBrownProperSingletonEvaluation.lean`: a single evaluated-mate
equality, before any singleton invertibility assertion. Its coefficient comparison is
fixed by a geometric mate equation. This is the specific below-level identification
used in Zheng Lemma 5.13.

`lem-pur-etale-brown-open-singleton-evaluation` in
`lean/Sheaf/Paper/EtaleBrownOpenSingletonEvaluation.lean`: the open singleton
square, for a coefficient comparison fixed by its open-adjunction mate. Its proof
requires no proper singleton isomorphism, so it is independent of the proper step.

`def-pur-etale-constant-module-restriction`: a definition node attached to the already
constructed `AlgebraicGeometry.Etale.SystemProjection.constantModule`, with no new Lean
declaration or hole. It separates sectionwise scalar restriction from unrelated
compact-support coherence. The realization node cites it instead of the broad system
projection data node.

The change record is `coord/changes/H6-etale-brown-dependency-granularity.md`. No
existing Lean interface is changed and there is no forced adaptation.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
