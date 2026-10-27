## What changed

Replaced the hole in `WeilConjectures.coef_qbar_verdier` by an assembly of the four
separate source results in the retained proof: finite-origin duality and evaluation,
internal Hom, exceptional descent, and the exceptional origin of the dualizing object.
The three retract equations are proved directly from evaluation naturality and
naturality of biduality and its inverse in `core_complete`.

Extracted the existing public data declarations into `CoefQbarVerdierData`, publicly
re-exported by the original module, so these separate results can import their unchanged
interfaces without an import cycle. The finite record and comparison definitions remain unchanged. The `Duality` and
`Exceptional` wrappers are subtypes of their original data records satisfying their
original property predicates, with explicit projection accessors. The full data module
compiled in 50.2 seconds.
No target or adopted source-library declaration is changed.

Added general categorical constructions for the opposite pair category and descent of
compatible adjunction units and counits. The latter is a complete proof, including finite
component formulas, using the already proved upstream StageSystem APIs. It avoids a
second construction via additive Hom-colimit equivalences. Earlier individual checks compiled the core retract proofs, internal-Hom finite
transpose, and assembly. The latest complete packet check is still being repaired
after the shared data module exceeded the compile limit.
The packet keeps the original finite fields and mathematical propositions; the two
wrapper representations change with their projection API preserved.

## Proved and sorry left

The original module had one hole, `WeilConjectures.coef_qbar_verdier`. Its body now
contains a complete assembly proof. This is a decomposition, not a net hole reduction.
The delivery currently adds four holes, all in named public theorems in separate modules:

- `WeilConjectures.CoefQbarVerdier.core_descent`,
  node `lem-coef-qbar-verdier-core-descent` (source steps 1–4).
- `WeilConjectures.CoefQbarVerdier.internal_hom_descent`,
  node `lem-coef-qbar-verdier-internal-hom` (source step 5).
- `WeilConjectures.CoefQbarVerdier.exceptional_descent`,
  node `lem-coef-qbar-verdier-exceptional-descent` (source steps 6–9).
- `WeilConjectures.CoefQbarVerdier.dualizing_descent`,
  node `lem-coef-qbar-verdier-dualizing-descent` (source step 9).

Each has its source and full intended argument in its docstring and node. Each is a
strict part of the original conclusion, rather than a renamed statement of the whole
conclusion. There are no holes in definitions or private declarations. The generic
adjunction constructor and its component formulas compile without holes. The three
retract equations compile without holes. The common-stage permitted-Hom lemma and the
exceptional and dualizing result
signatures compile against the published interfaces. `finite_data_exists` constructs the complete finite record from the simultaneous
rational Verdier theorem and rational Hom identifications; its standalone check compiled
in 39.7 seconds. It adds no hole. A finite evaluation-transpose lemma
is also included: its bijection is postcomposition with the duality-to-Hom comparison
followed by the inverse tensor-Hom adjunction. Its generic-helper probe compiled in
12.7 seconds; the sole unused-section-instance
warning was addressed with an explicit omit.
A separate unchanged QbarCurveDuality consumer check timed out at 60 seconds while
generating an artifact; it produced no type error. Consumer validation against the
complete repaired dependency set remains pending.
Consumer projection types retain their meanings; no consumer adaptation is claimed.

## No longer needed

The route does not use `lem-coef-qbar-adjunction-hom-descent` or
`lem-weil-pbc-adjunction-of-natural-bijection`: the finite units and counits descend as
compatible natural transformations, and the triangle identities are checked after
finite inclusion. It does not use `lem-coef-rational-retract-evaluation` for the three
recorded retract equations: these follow from naturality in the same category.
These are pruned proof dependencies only; no adopted source declaration is removed.

All the remaining original finite-coefficient, coefficient-category, tensor/Hom,
scalar-comparison and exceptional-operation dependencies remain needed by the separate
source results or the public interfaces. The data module removes four unused private proof imports:
`StageSystemFunctorDescent`, `CoefIntegralFiniteExtension`,
`IntegralOperationsScalarComparisons` and `SfScalarExtensionComposition`.
The full data block with the subtype repair compiled in 50.2 seconds; packet and
consumer validation remain pending.

## Where the brief, the DAG or earlier work was wrong

The live item is present despite its earlier quarantine row; it is preserved and
repaired, not withdrawn. The original data block is costly to recompile because its dependent record fields
repeat transported coefficient structures. A synchronous profiling check compiled the
whole block in 59.2 seconds, but delivery measured 63 seconds. The subtype wrapper repair subsequently compiled in 50.2 seconds. Packet and consumer
validation remain pending.

The adjunction portion of the DAG can be shorter: its compatible finite units and
counits already give the adjunction directly through StageSystem natural-transformation
descent. The retract portion also needs only naturality. The unit route and all
mathematical clauses of the conclusion are retained. No statement is disputed.

## New nodes

`lem-coef-qbar-opposite-stage-pairs`: the inverse opposite associator defines the opposite
stage system; reversing representatives gives the equivalence with the opposite pair
category. Used by core duality descent.

`lem-coef-qbar-stage-adjunction-descent`: compatible finite units and counits descend and
satisfy the triangle identities on literal finite-stage objects. Used by exceptional
descent. This node has no holes.

`lem-coef-qbar-verdier-core-descent`: the finite-origin duality and evaluation equations
before retract restriction; `core_complete` proves the restriction formulas.

`lem-coef-qbar-verdier-internal-hom`: the internal-Hom identification and actual evaluation
transpose universal property; every common-stage pair is permitted by finite closure.

`lem-coef-qbar-verdier-exceptional-descent`: the actual coherent exceptional system and
its normalized formula for the two specified dualities.

`lem-coef-qbar-verdier-dualizing-descent`: the same omega is the exceptional image of the
actual coefficient unit, with the same finite system.

Change record: `coord/changes/V1-qbar-verdier-descent-interfaces.md`.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
