## What changed

Restored and checked the complete ordinary tensor transitions, quotient augmentation,
ordinary pullback mate, transition compatibility, and K-flat descent from the prior
G4 implementation in Sheaf.Paper.ProEtaleConstantReductionTower. The six filled
declarations have their original signatures. The reduction pair uses the existing
DerivedReductionModelData API; its universal property determines the chosen data.

The augmentation is the universal derived lift, with proved normalization and equality
to the former uniqueness choice. ModelPullNormalized packages the original displayed
normalization without repeatedly unfolding concrete functor expressions. Its
specialization to ReductionPullNormalized has the same equation.

The definition changes and all direct consumers are recorded in
coord/changes/T4-constant-reduction-universal-model.md. No consumer or source-library
file is modified.

## Proved and sorry left

Closed six of the seven original holes, all in namespace
AlgebraicGeometry.Scheme.OrderedExchange, node lem-sp-completion-mate-comparison:

- step_existsUnique
- ordinaryAugmentation_existsUnique
- augmentation_existsUnique
- ordinaryReductionPullInv_isIso
- levelPullIso_transition
- reductionPullIso_existsUnique

The only original hole left is
AlgebraicGeometry.Scheme.OrderedExchange.projection_isIso
(node lem-sp-completion-mate-comparison). No hole is added and no statement is split off.
All private helpers and the new model-data and normalization theorems are proved.
The existing quotient_comm, reductionModule_additive and reduction_exists proofs remain
complete. Five of the six filled declarations have only propext, Classical.choice and
Quot.sound in their axiom output. The derived pullback descent additionally uses
existing unfinished K-flat infrastructure; this is a proof from the stated dependencies.

Validation: lcompile.py compiled the final item and the unchanged live consumers
CompletedProjectionCoherence and CompletedPullbackUnitTower in the same batch
(37.0, 10.9 and 13.9 seconds). A separate probe compiled the definitional equality
between ReductionPullNormalized and the complete original displayed equation, and
printed the six axiom lists described above. Temporary verification files are excluded
from the delivery. Existing public theorem signatures are unchanged; all Lean lines
fit within 100 characters.

## No longer needed

No import is removed from the current live module. No DAG node or module is withdrawn.
The old private scalarReduction_map_quasiIso and kFlat_leftDerived_exists helpers
are superseded by the bundled resolving-class construction; their results remain
proved in the new construction.
The proposed fixed-index PerfectConstantProjectionEvaluation module and its node were
removed from this packet before delivery; they are not existing library sources.
The original projection_isIso hole remains in place. The unit route and generic
completionMateComparison reexport are retained.

## Where the brief, the DAG or earlier work was wrong

A previous G4 implementation contained proofs of the six original holes, but was
removed in a batch rollback. Restoring and verifying those proofs avoids duplicating
the argument. Its finite-level projection theorem still had a hole, so it is not
claimed as a proof here. The early delivery gate correctly refused the packet that
added that split, and it has been removed.

The original small pro-etale site has unequal object and morphism universes; the
generic equal-universe totalization theorem cannot be applied directly. The completed
coefficient projection theorem uses a different coefficient ring. Neither supplies
the remaining constant-coefficient projection claim without additional comparisons.
No false statement or target discrepancy is asserted.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
