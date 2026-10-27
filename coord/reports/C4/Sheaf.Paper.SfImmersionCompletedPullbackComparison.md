## What changed

Proved ImmersionCompletedPullback.completedProjection_compatibility, preserving its
statement and both specified maps. The proof first works over an arbitrary adic
coefficient datum, then specializes to the original integral datum. Evaluation of
the derived constant/limit counit gives the projection of the pulled augmentation.
The K-flat computing counits identify its finite evaluation with the scalar unit;
naturality extends that identity to all derived objects. The transition equation
combines the actual Rlim projection law with the existing evaluation-interchange
and quotient-transition laws. Proved helpers contain these calculations.

Extracted the generic finite calculations into the new module
SfImmersionFiniteNormalization to reduce kernel checking time in the item. It
provides the proved public theorem sfCompletedReductionAugmentation_level_unit;
all other extracted calculations remain proved private helpers. The item imports
this module for its proof, with private access to the existing generic helpers.
The helper module imports the existing proved counit/evaluation normalizations.
Extracted the already-proved abstract Roos normalization into
SfImmersionRoosNormalization, including its proved public resolution uniqueness
lemma sfRoosComparison_ext, to reduce checking time further. Updated the item's
proof plan and dependencies and added both helper nodes. The final extraction also
moves the original private actual/intrinsic completion transports, product-coordinate
normalizations, and exact-derived-counit normalization into those helper modules.
Their statements and proofs are preserved. The new projection proof explicitly
identifies its coefficient type and uses the default transparency settings.
No existing public signature, definition body, public import, or shared module changed.

## Proved and sorry left

Original holes: 3. Closed: 1. Added: 0. Remaining: 2.

Closed:

- AlgebraicGeometry.Scheme.ImmersionCompletedPullback.completedProjection_compatibility.

Unchanged original holes, both attached to
lem-sf-immersion-completed-pullback-comparison:

- AlgebraicGeometry.Scheme.ImmersionCompletedPullback.rlimComparison_roos.
- AlgebraicGeometry.Scheme.ImmersionCompletedPullback.immersion_completed_pullback_comparison.

All added helpers and both new public theorems are proved. No new sorry statement
or axiom is introduced.
The scalar-unit calculation compiled independently in 16.9 seconds. The initial
helper-plus-item compile typechecked the proofs but took 63 seconds
for the item. A later 64-second run prompted profiling: kernel checks of existing
normalization proofs account for a substantial part of the time. These private
proofs were extracted further. All three final modules were accepted by lcompile.py. The item compiled in
41.3 seconds. Both helper modules compile with zero holes; no profiling or
unsafe reducibility overrides remain. The projection theorem uses explicit
associativity and permissive rewrites only where the coefficient aliases require them.

## No longer needed

No mathematical dependency or existing module is withdrawn. Removed the helper's
unused CompletedPullbackReductionCoherence import; the item retains it for its
actual projection-transition calculation. The item's direct
LevelwiseAdicTruncations import moves to the finite helper module that uses it.
The direct RightDerivedFunctor.ShortExactPullback import moves to the Roos helper
that uses its UnitQ normalization. The two remaining original
holes retain their existing plans and dependencies. The projection proof uses
existing generic adjunction, evaluation, and scalar-unit normalizations directly;
it introduces no new unproved statement. No dependency is removed from the
import closure: the ordinary imports of ExactTowerAugmentedCounitEvaluation and
StratumCompletionUnitRestriction were replaced by their proof-only import-all
forms, and the duplicate ordinary stratum import was removed.

## Where the brief, the DAG or earlier work was wrong

The earlier proof-origin text recorded three remaining holes. This delivery
updates it to reflect the projection-compatibility proof and two remaining holes.
The current source exists despite its historical rework/quarantine row; it was
preserved, with every declaration and its Lean attachment intact. No archive is
withdrawn and no dependency is deleted on the basis of that row.

## New nodes

- lem-sf-completed-reduction-augmentation-level-unit, in
  Sheaf.Paper.SfImmersionFiniteNormalization: a proved scalar-unit normalization,
  strictly the evaluated-augmentation step of projection compatibility. Zero holes.

- lem-sf-roos-comparison-resolution-uniqueness, in
  Sheaf.Paper.SfImmersionRoosNormalization: proved uniqueness from equality on
  K-injective resolutions. Its private helpers retain the existing normalized
  comparison construction. Zero holes.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
