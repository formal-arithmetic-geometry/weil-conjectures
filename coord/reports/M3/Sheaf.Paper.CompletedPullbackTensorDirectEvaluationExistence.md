## What changed

Repaired and proved `WeilConjectures.completedPullbackTensorDirectEvaluation_exists`
in `Sheaf.Paper.CompletedPullbackTensorDirectEvaluationExistence`: require the
coefficient map to equal the canonical constant-section map. Compose Mathlib's
pushforward comparisons and compare the two scalar maps componentwise. The result
acts as identity on every section. A private `SectionwiseIdentity` predicate
and the proved private helpers
`sectionwiseIdentity_trans`, `pushforwardComp_sectionwise` and
`pushforwardCongr_sectionwise` assemble the section formulas at the level of
arbitrary ringed sites, without unfolding coefficient-ring constructions.
The existing arbitrary-map uniqueness proof, base direct-image definition,
and public import are unchanged.

Adapted only the helper application in
`Sheaf.Paper.CompletedPullbackTensorComparison`, passing its existing
`pullbackTensorSequenceRing_eq` proof. Its declaration signatures and definitions
remain identical. Updated the item's node, including its statement correction
and sole-citer audit. The change record is
`coord/changes/M3-canonical-sequence-direct-evaluation.md`.

Validation: the item compiled cleanly through `lcompile.py` in 17.0 seconds.

## Proved and sorry left

The item started with one hole:
`WeilConjectures.completedPullbackTensorDirectEvaluation_exists`
(node `lem-pur-completed-pullback-tensor-direct-evaluation-existence`).
Its former arbitrary-map statement is false and is corrected, not claimed proved.
The repaired canonical-map theorem is proved completely; zero holes remain in
the item. The already-proved
`WeilConjectures.completedPullbackTensorDirectEvaluation_unique` is unchanged.
Added zero holes and split off zero statements. No definition contains a hole.

The forced consumer adaptation leaves its 24 pre-existing holes unchanged,
all attached to `def-pur-completed-pullback-tensor-comparison`:

- `WeilConjectures.pullbackTensorReductionModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorSequenceInverseEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorRoosModel_existsUnique`
- `WeilConjectures.pullbackTensorPullbackTower_existsUnique`
- `WeilConjectures.pullbackTensorTensorTower_existsUnique`
- `WeilConjectures.pullbackTensorIntegralPullbackModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionGood`
- `WeilConjectures.pullbackTensorIntegralTensorModel_existsUnique`
- `WeilConjectures.pullbackTensorSequenceCochain_existsUnique`
- `WeilConjectures.pullbackTensorSequenceGood`
- `WeilConjectures.pullbackTensorSystemComparison_existsUnique`
- `WeilConjectures.pullbackTensorComparisonCounits`
- `WeilConjectures.pullbackTensorSystemComparison_evaluation`
- `WeilConjectures.pullbackTensorSystemComparison_associativity`
- `WeilConjectures.pullbackTensorSystemComparison_braiding`
- `WeilConjectures.pullbackTensorSystemComparison_unit`
- `WeilConjectures.pullbackTensorQuotientOrdinary_existsUnique`
- `WeilConjectures.pullbackTensorFiniteGood`
- `WeilConjectures.pullbackTensorQuotient_existsUnique`
- `WeilConjectures.canonicalFinitePullbackTensor_quotient`
- `WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique`
- `WeilConjectures.canonicalIntegralPullbackTensor_scalar`
- `WeilConjectures.canonicalRationalPullbackTensor_scalar`

## No longer needed

None. No imports, modules or nodes are removed. Both existing declared
statement dependencies are used: the sequence-system canonical coefficient map
and the sequence-site evaluation ring identifications. No further dependency
or split lemma is needed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier split generalized the ring map to an arbitrary ρ while retaining
the canonical coefficient action on the right. Those actions can differ, so
the identity on sections need not be linear. For f = id and an unramified
quadratic coefficient extension, compatible quotient Frobenius automorphisms
provide a twisting ρ; on the regular module the identity would equate twisted
and ordinary multiplication, contradicting the nontrivial residue automorphism.
This was already marked STATEMENT-DISPUTED by B5.

Stacks Tags 03D1 and 03D6 (sites-modules.tex, lemma-pushforward-module and
definition-pushforward) define the action by the specified structure map.
The original node's words and its sole consumer already intend this canonical
map. The repair records that condition explicitly. The sole citer,
`def-pur-completed-pullback-tensor-comparison`, still holds because
`pullbackTensorSequenceRing_eq` identifies its chosen map with that canonical map.
The canonical comparison works at n = 0, on empty sites, and for identity maps:
its construction is uniformly the identity on sections, without nonemptiness
or nonzero assumptions. No target statement or definition changes.

## Forced adaptations

`Sheaf.Paper.CompletedPullbackTensorComparison` is held by J3. The only changed
lines are the call at line 439, adding
`(pullbackTensorSequenceRing_eq l E f)` as the new final proof argument.
The existing equality is the exact hypothesis required by the repaired helper;
no other line, signature or visibility changes.

## Forced adaptations

### Sheaf.Paper.CompletedPullbackTensorComparison
Original already fails against the compiled baseline (pre-existing):
```

NOT ACCEPTED: this compile took 75 s > 60 s, the limit for one file (every file must compile alone within 60 s). The compile was allowed to run up to 120 s only so that the slow declarations finish and report: the messages above show them (to see where the time goes, add `set_option profiler true` with `set_option profiler.threshold 100` at the top of the file while debugging, and remove them before delivering). The cause is usually a definition that is expensive to unfold; change it, not the limit.

[75.0 s]
```
Adapted module compiled in the delivered set.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
