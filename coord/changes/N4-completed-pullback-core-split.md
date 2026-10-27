# CompletedPullbackTowerRealizations construction-prefix extraction

## Reason

The original integral pullback model hole is proved, with no new holes. Profiling and
conversion improvements were attempted first: private comparisons were packaged with
component lemmas, the descent component calculation was proved in a separate small
module, and large constructions were kept folded using local transparency attributes.
The combined file still took 67 seconds; earlier delivery probes took 62.6 and 71 seconds.
Following stage-3 step 3a, extract the existing construction prefix into
`Sheaf.Paper.CompletedPullbackTowerCore` and re-export it. All 51 moved public declaration
names, signatures and definition bodies are preserved. Their docstrings only change the
blueprint identifier to the new core node. The unique-choice wrapper retains its existing
reducibility attribute. No target or mathematical definition changes meaning.

The moved declarations are:

- `WeilConjectures.pullbackTensorUniqueChoice`
- `WeilConjectures.pullbackTensorSequenceSmall`
- `WeilConjectures.pullbackTensorCalculus`
- `WeilConjectures.pullbackTensorSequenceBase`
- `WeilConjectures.pullbackTensorSequenceBase_continuous`
- `WeilConjectures.pullbackTensorSequenceRing_existsUnique`
- `WeilConjectures.pullbackTensorSequenceRing`
- `WeilConjectures.pullbackTensorSequenceDirect`
- `WeilConjectures.pullbackTensorSequenceDirect_rightAdjoint`
- `WeilConjectures.pullbackTensorSequenceInverse`
- `WeilConjectures.pullbackTensorSequenceAdjunction`
- `WeilConjectures.pullbackTensorSequenceInverse_exact`
- `WeilConjectures.pullbackTensorSequenceInverse_additive`
- `WeilConjectures.pullbackTensorSequenceInverse_limits`
- `WeilConjectures.pullbackTensorSequenceInverse_colimits`
- `WeilConjectures.pullbackTensorSequenceDerived`
- `WeilConjectures.pullbackTensorOrdinaryLimit`
- `WeilConjectures.pullbackTensorOrdinaryLimit_rightAdjoint`
- `WeilConjectures.pullbackTensorOrdinaryReduction`
- `WeilConjectures.pullbackTensorOrdinaryAdjunction`
- `WeilConjectures.pullbackTensorOrdinary_additive`
- `WeilConjectures.pullbackTensorOrdinaryReduction_additive`
- `WeilConjectures.pullbackTensorOrdinaryLimit_additive`
- `WeilConjectures.pullbackTensorConstantLimit`
- `WeilConjectures.pullbackTensorConstantLimit_additive`
- `WeilConjectures.pullbackTensorTowerHasDerived`
- `WeilConjectures.pullbackTensorLevelAdditive`
- `WeilConjectures.pullbackTensorTowerKInjectives`
- `WeilConjectures.pullbackTensorTowerQ`
- `WeilConjectures.pullbackTensorLimitUnit`
- `WeilConjectures.pullbackTensorReductionModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionModel`
- `WeilConjectures.pullbackTensorFiniteAdjunction`
- `WeilConjectures.pullbackTensorReductionEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorReductionEvaluation`
- `WeilConjectures.pullbackTensorSequenceDirectEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorSequenceDirectEvaluation`
- `WeilConjectures.pullbackTensorSequenceInverseEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorSequenceInverseEvaluation`
- `WeilConjectures.pullbackTensorRestrictedLevel`
- `WeilConjectures.pullbackTensorRestrictedTower`
- `WeilConjectures.pullbackTensorRoosAugmentation`
- `WeilConjectures.pullbackTensorRoosAugmentation_condition`
- `WeilConjectures.pullbackTensorRoosUnit`
- `WeilConjectures.pullbackTensorRoosModel_existsUnique`
- `WeilConjectures.pullbackTensorRoosModel`
- `WeilConjectures.pullbackTensorReductionEvaluationComplex`
- `WeilConjectures.pullbackTensorInverseEvaluationComplex`
- `WeilConjectures.pullbackTensorPullbackTowerLevel`
- `WeilConjectures.pullbackTensorPullbackTower_existsUnique`
- `WeilConjectures.pullbackTensorPullbackTower`

## Old

The existing module's public imports, verbatim:

```lean
public import Sheaf.Paper.FinitePullbackTensorConstruction
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
```

The 51 declarations above occurred in that module's prefix, ending with
`pullbackTensorPullbackTower`. Their exact signatures and bodies are retained in the
new core file; this change does not replace any definition body.

## New

The existing module keeps those public imports and re-exports the new core:

```lean
public import Sheaf.Paper.FinitePullbackTensorConstruction
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.CompletedPullbackTowerCore
```

`CompletedPullbackTowerCore` contains the unchanged prefix, with its original public
imports and proof imports. The item retains the tensor and realization declarations,
plus the completed proof and its proved private comparison helpers. Proof imports used
only by the prefix move with it. The new categorical descent lemma is imported privately.
Four pre-existing holes move to the core under the same declaration names; six remain
in the item. No hole is introduced by the file split.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | B4 | Unchanged source compiled successfully against the split, then its temporary sandbox copy was removed. Every public name is re-exported with the same signature. |
| `Sheaf.SixFunctors.OrdinaryOpenFiniteEvaluation` | unclaimed | Its original `import all` could no longer see the relocated private ring-map lemma. Add one proof-only `import all` of the new core; all signatures and proof text stay unchanged. |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | N4 | Imports and re-exports the new core; proves its original integral pullback model hole. |

The only consumer adaptation is the one added proof import above. The original compiler
error at `OrdinaryOpenFiniteEvaluation.lean:42:6` was
`Unknown identifier pullbackTensorSequenceRing_eq`. Its `direct_eq` proof then had an unsolved equality
between sequence pushforward and varying-ring pushforward. The added import exposes
the exact relocated private theorem; no proof or signature is changed. The adapted
consumer then compiled successfully. The final packet also compiled the core, the
component lemma and the item. The moved prefix matches the current shared source byte
for byte after restoring its old blueprint identifiers.

No definition used by a target changes its
mathematical value or signature.

## Status

landed 20261027T050627-L-246468 2026-10-27 (merge of deliver/N4/Sheaf.Paper.CompletedPullbackTowerRealizations)
