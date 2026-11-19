# Nested experiments: PR #1627

Case: AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor and generated
_proof_1/_proof_2 fields. Snapshot: Lean 4.35.0, master revision
1ef1fddac73e, one thread, synchronous elaboration,
maxHeartbeats 10000000.

## Baseline and preserved context

The old prefix is 107.63 CPU s, 109.17 wall s, and 7,781,816 KB peak RSS;
the generic-helper control is 9.38 CPU s, 9.85 wall s, and 1,837,544 KB.
The three generated field checks are 27.8, 55.3, and 14.6 s. The retained
consumer is each generated functor-law proposition and its dependent id
proof argument; the final declaration type conversion is immediate.

## Experiment A: representation symmetry status

The old value constructs a concrete Functor.mk with carrier, object/map,
and generated law fields. The after value uses IsoAlgebra.liftOfStr. These
are two valid constructions of the same mathematical functor, but the
generic helper changes the proof construction and the imported abstraction
boundary at once. No type-preserving raw/raw versus abstracted/abstracted
matrix was available without manually inventing proof constants, which
section 3.4 forbids. A is therefore recorded as an API-level negative
control, not as a DefEq symmetry result.

The explicit generated-proof replay in probes/nd/G2C-GeneratedProofAudit.lean
keeps the original law propositions and separates value checks from final
type conversions. It records id argument-1 proposition-domain conversions
of 7,508 ms for _proof_1 and 33,863 ms for _proof_2.

## Experiment B: nesting amplification status

The generated law has a dependent forall domain: the proposition passed to
id becomes the domain of the next proof argument. This is the real nested
consumer, but the old declaration provides only one provider depth. Adding
synthetic Layer0--LayerN classes would change the functor-law proposition
and violate section 2.1. The 7.508/33.863-second domain checks therefore
localize nesting but do not establish a controlled B trend.

## Experiment C: repeated-field fanout

The three generated checks are the required repeated-field observation:

| Generated field | Value check | Final type conversion |
|---|---:|---:|
| _proof_1 | 20.341 s replay (27.8 s in situ) | 0 ms |
| _proof_2 | 33.929 s replay (55.3 s in situ) | 0 ms |
| remaining generated field | 14.6 s in situ | not separately replayed |

All three fields are forced by the concrete Functor.mk value; none is
unused. The first two share the same id/application shape, but their
proposition types have different binder sizes and different nested
parameters. The evidence supports repeated law-field work, while the
non-monotone 27.8/55.3/14.6-second values show that field count alone is
not a sufficient explanation. A valid C1/C2/C3 matrix would require
rebuilding the functor type and hence would not be the same consumer.

## Experiment D: provenance audit

LEFT: each old law field is generated while elaborating a concrete
Functor.mk. The object/map data use frobeniusPowPullback and the concrete
WeilSheaf.frobeniusPullback representation; the law proof is wrapped in an
id application whose second argument has a dependent proposition domain.

RIGHT: the expected law type is stored with the generated declaration. Its
proposition is elaborated from the same concrete functor parameters and is
not rewritten by local instance priorities. The first timed divergence is
the dependent id proof argument, not the final theorem type. The historical
inner candidate is frobeniusPowPullback versus WeilSheaf.frobeniusPullback;
the current replay did not extract a single first leaf below the id domain.

The fixed generic helper moves the data-bearing object behind IsoAlgebra's
abstract interface and avoids generating these concrete law checks. That is
strong provenance evidence but not a one-factor alignment proof.

## Matched fast control and interpretation

The after generic-helper declaration has the same functor result type and
coefficient context, but no generated checks above the profiler threshold.
It is the matched fast control for field construction; the construction
change is explicitly kept separate from the nested Kernel result.

Outcome: C has strong repeated-generated-field evidence at Level 1, with
the same dependent id-domain mechanism in two fields. A and B remain
inconclusive because a valid raw/abstract symmetry or depth matrix would
require inventing or changing proof/data representations. D identifies
concrete Functor.mk law generation as the producer.
