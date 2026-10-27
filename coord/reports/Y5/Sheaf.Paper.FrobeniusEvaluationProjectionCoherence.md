## What changed

Filled eight proofs in `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence` and
added the proved common-stage tensor braiding descent theorem in
`Sheaf.Paper.CommonStageTensorBraidingNaturality`. Existing signatures, definitions
and public imports are unchanged. All added helpers are proved.

The evaluation proofs combine the existing normalized Hom-first evaluation
naturality with the specified signed braiding and the existing argument-first
pullback evaluation equation. A generic categorical calculation cancels the
contravariant inverse Weil map against the forward Weil map, then substitutes
that pullback equation. Integral braiding naturality is the proved private helper
in `CompletedTensorHomTranspose`, reused with `import all`; its separated-scheme
public transpose theorem is not used. Rational braiding naturality follows from
`localizedTensorBraiding_naturality`. The new common-stage theorem represents both
arrows at one field, applies the tensor and braiding representative formulas,
cancels their comparison maps, and applies rational naturality.

`ordinary_projection` uses the projection mate of the supplied lifted adjunction.
`open_projection` constructs its prescribed inverse gamma as a lifted projection
mate, reflects invertibility through the forgetful functor, and inverts it.
`compact_projection` composes the ordinary and open projections and the supplied
pullback compositor. Carrier calculations identify exactly the stated maps.
`OpenSquare.realized_open_square` applies the supplied coefficient-representative
function to the existing `open_square` equality. The two refinement proofs use
faithfulness and conjugation by the supplied refinement isomorphisms.

The item node records the evaluation argument and its actual dependencies.
No statement repair, definition repair, or consumer adaptation is introduced.

## Proved and sorry left

Closed eight of the ten input holes, in namespace
`WeilConjectures.PodEvaluationProjection`:

- `rational_evaluation`
- `common_evaluation`
- `ordinary_projection`
- `OpenSquare.realized_open_square`
- `open_projection`
- `compact_projection`
- `refinement_compatibility`
- `refinement_transport`

The two original holes left are `OpenSquare.transport_exists` and
`OpenSquare.open_square`, both attached to
`lem-pod-frobenius-evaluation-projection-coherence`. Their statements and complete
proof docstrings are unchanged. Added zero holes; split off zero unproved
statements. The new theorem `WeilConjectures.commonStageTensorBraiding_naturality`
is proved. Existing imported evaluation obligations remain existing dependencies;
no duplicate evaluation statement is added.

## No longer needed

Removed unused private imports:

- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`
- `Sheaf.Paper.FixProjectionCompactificationComparison`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.Compactification.BaseChange`

The supplied projection interfaces already provide adjunctions, Weil lifts and
normalizations; no geometric compactification construction is needed for their
categorical conclusions. Refinement compatibility already supplies the underlying
identity. Realization applies a function to an equality. No module is withdrawn,
and no dependency still cited by a pending obligation is claimed globally pruned.
The pending open-square proof plan, its tensor/realization dependencies, and the
unit route are retained. No top-level tool approval is added or reordered.

In evaluation step 1, `sk-def-sf-operations` is replaced as a proof dependency by
the actual normalized evaluation declarations, localized braiding naturality,
the proved integral braiding helper, and the new common-stage descent theorem.
No site-perfectness or separatedness hypothesis is introduced.

## Where the brief, the DAG or earlier work was wrong

The existing normalized evaluation laws are Hom-first; the theorem here is
argument-first. The signed-swap naturality step must therefore be supplied rather
than applying Hom-first evaluation naturality directly. The common-stage symmetry
had component representative formulas but no standalone naturality declaration;
the new theorem proves precisely that descent step from rational naturality.
No false statement was found. The six categorical holes already described by the
Q3 report were still holes in the source supplied to this session; this packet
includes their proofs against that source and does not claim they were newly
invented mathematical reductions.

## New nodes

`lem-pod-common-stage-tensor-braiding-naturality` states and proves descent of
rational braiding naturality to arbitrary arrows of the actual common-stage
category. It is strictly a coefficient symmetry step, independent of Frobenius,
Weil structures, Hom comparisons and evaluation. Its node contains the finite-stage
proof, repository/blueprint duplicate searches and three kinds of Mathlib search.
No new sorry or change record is needed.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
