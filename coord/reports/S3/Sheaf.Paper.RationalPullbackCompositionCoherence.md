## What changed

The two original coherence theorems now assemble finite coefficient coherence, ordinary
rational tensor comparisons and completed/raw descent. Both predicate definitions and
both theorem signatures are preserved verbatim. The finite completed projection clause
is proved using the actual `limit.lift_π` equation after coefficient composition and
associativity, without exchanging inverse image and inverse limit.

Four genuine substeps are stated in separate modules, one theorem per module:
`RationalOrdinaryPullbackComposition`, `RationalOrdinaryPullbackIdentity`,
`RationalCompletedPullbackComposition`, `RationalCompletedPullbackIdentity`.
The ordinary statements assert the coefficient and tensor/derived comparison clauses
only. The completed statements take those specified ordinary witnesses and their
normalization equations as inputs and assert the remaining integral unit, raw fraction
and alpha compatibility clauses. The parent constructs their conjunctions and passes
exactly the same ordinary witnesses to the completed substeps. No split statement has
the whole parent conclusion.

The original helper definitions, their bodies and attributes, both predicate definitions,
and all existing declaration signatures stay in their original module verbatim. Each
new statement uses local let abbreviations for actual tensor sections and module scalar
multiplication. This makes their formulas self-contained without importing their parent
and without moving any existing declaration. No definition or public import changes.

Validation: all five delivered modules compile without warnings. The parent takes
45.4 seconds; the composition substeps take 46.1 and 56.4 seconds, and the identity
substeps take 5.8 and 4.4 seconds. Text comparison verified all existing helper and
predicate bodies and both original public theorem signatures verbatim, in place.

## Proved and sorry left

Two upper holes closed by decomposition, with complete Lean assembly proofs:

- `AlgebraicGeometry.Scheme.rationalPullbackCompositionCoherence`
  (`lem-per-rational-pullback-composition-coherence`).
- `AlgebraicGeometry.Scheme.rationalPullbackIdentityCoherence`
  (the same existing node).

There are zero holes in the assigned module and four new lower holes, each with its
source, complete proof in words and new DAG node:

- `AlgebraicGeometry.Scheme.rationalOrdinaryPullbackComposition`
  (`lem-per-rational-ordinary-pullback-composition`).
- `AlgebraicGeometry.Scheme.rationalOrdinaryPullbackIdentity`
  (`lem-per-rational-ordinary-pullback-identity`).
- `AlgebraicGeometry.Scheme.rationalCompletedPullbackComposition`
  (`lem-per-rational-completed-pullback-composition`).
- `AlgebraicGeometry.Scheme.rationalCompletedPullbackIdentity`
  (`lem-per-rational-completed-pullback-identity`).

This is a decomposition, not an unconditional proof: two holes closed, four added,
net minus two holes closed. The proof still rests on these statements and the
pre-existing coefficient-coherence dependencies. No `sorry` occurs inside a definition.

Edge cases checked from the formulas: empty charts and the zero module give equality
of the unique/zero sections; either zero tensor scalar makes both tensor formulas zero;
identity chart transport uses the specified pullbackId map rather than definitional
identity. No structural coefficient map is assumed an isomorphism, no completeness
unit is cancelled outside the supplied integral objects, and raw localization includes
all integral objects and all denominators. No realization faithfulness is assumed.

## No longer needed

No original import or global module is withdrawn. The four former high-level proof
dependencies are now accounted for by the more precise ordinary and completed/raw
substeps; the coefficient part uses the already proved finite/completed coefficient
coherence theorem. The original statement dependencies and unit route are retained.

The old eight tool_uses entries (site-morphism composition, ringed derived monoidal
comparisons, canonical tensor pullback, localization inverse image, completion reflector,
constant/completed equivalence, ringed pushforward completion and reflected compositor
normalization) are removed from the parent node because the parent assembly no longer
applies these tools directly. The retained normalization dependencies of the four
substeps still account for the original mathematical argument.

## Where the brief, the DAG or earlier work was wrong

The current server queue is a stage-3 proof item with two holes. The historical build
error records a bad import of RationalRealizationPullbackComparison; the unchanged
source compiles against the published artifacts in 57.8 seconds, so that recorded
dependency failure is not reproduced by the current baseline. The quarantined source
was retained and no archive was withdrawn. There is no import-collision rename to repair.

The node's ordinary normalization dependency is stated for the localization presentation
B[1/varpi], whereas the parent uses the supplied continuous E coefficient sheaves and
arbitrary normalized realization records. Its derived model equations are stated on
flat-term K-flat representatives, while the parent records the resulting computation
counit equation on all complexes. The ordinary transport/counit substeps make this
interface gap explicit instead of identifying those records by definitional equality.
The completed substeps retain the separate cancellation and all-fraction descent
arguments. No mathematical statement or fixed unit route has been changed.

Separate baseline checks of the two unchanged direct consumers report runtimes over
the 60-second limit: `RationalScalarMixedUnitCancellation` takes 60.9 seconds and
`RationalRealizationScalarCoherence` takes 70.4 seconds against the published baseline.
These baseline checks use no delivery overlay. The delivered five modules pass the
limit. The packet changes no existing interface and carries no consumer adaptations.

## New nodes

`lem-per-rational-ordinary-pullback-composition` records the ordinary coefficient,
module tensor and derived counit part of the composition argument.

`lem-per-rational-ordinary-pullback-identity` records the corresponding ordinary identity.

`lem-per-rational-completed-pullback-composition` records the strict completed unit,
raw fraction descent and alpha equation given the specified ordinary compositor.

`lem-per-rational-completed-pullback-identity` records the corresponding completed/raw
identity given the specified ordinary identity.

The original node's Lean attachment is unchanged. Its proof and proof_deps follow the
assembly, using the four named substeps and finite coefficient coherence. Statement
text, statement dependencies, both predicates, all helper definitions and the fixed
perverse-unit route stay as before. No change record is needed: no existing definition,
statement, attribute, public import or declaration location changes.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalCompletedPullbackComposition": "a627a19c98206a43ea30ee602662d7c83da924ed", "Sheaf.Paper.RationalCompletedPullbackIdentity": "cb030751cd0d61876f24eaedb79d71fd57a7d09a", "Sheaf.Paper.RationalOrdinaryPullbackComposition": "88d480135646ac9fe17f481a88453e0d95ff5c69", "Sheaf.Paper.RationalOrdinaryPullbackIdentity": "cbb8fbbb6f0c701352e66dc75cc8790f008bbcf0", "Sheaf.Paper.RationalPullbackCompositionCoherence": "e56b6037fabb13b40d3fd7a77e4214009cdfc04b"}, "results": {}, "time": "2026-10-28T01:01:14+0800", "transitive": 0, "version": 1}
```

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
