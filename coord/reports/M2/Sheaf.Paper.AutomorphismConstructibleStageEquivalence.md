## What changed

Only `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` is changed. Its public
statements and definitions are preserved. The general isomorphism field-transport
interface supplies the integral, rational and algebraically closed equivalences.
Finite constructibility uses the termwise isomorphism pullback theorem; linearity
is transported through the fixed-scalar realization. The finite restricted shift
is checked using Mathlib's fully faithful shift-lift component formula. Pulling
back the witnessing strata and local trivializations gives the prescribed strata.
Completeness and the actual completion unit use the existing normalization
interface, together with the equivalence of intrinsic and legacy completeness.
The entire reduction-system comparison specializes its existing general interface.

All added imports are private proof imports. No source-library module is changed.
Local transparency and instance settings avoid unfolding the chosen realization
and derived pullback constructions during categorical reasoning.

Validation: all 38 original public signatures and the ordered public imports
match the repository source. No added Lean line exceeds 100 characters. The
field-transport import-direction check passes. The delivery tool performs the
single-file compile, preflight and axiom checks before pushing.

## Proved and sorry left

The original module has 22 holes; 10 are closed and 12 are retained. No holes
are added. The closed declarations are:

- `automorphismConstructibleStage_units`
- `automorphismConstructibleStage_finite`
- `automorphismConstructibleStage_integral_rational`
- `automorphismConstructibleStage_qbar`
- `automorphismConstructibleStage_finite_linear`
- `automorphismConstructibleStage_strata`
- `automorphismConstructibleStage_completion`
- `automorphismStage_inverseSquare`
- `automorphismConstructibleStage_completion_unit`
- `automorphismConstructibleStage_reduction`

Existing holes retained, all attached to
`lem-sf-automorphism-constructible-stage-equivalence`:

- `automorphismStageIntegralSquare_existsUnique`
- `automorphismStageRationalSquare_existsUnique`
- `automorphismStageQbarSquare_existsUnique`
- `automorphismConstructibleStage_finite_coherence`
- `automorphismConstructibleStage_comparison_system`
- `automorphismConstructibleStage_square_reduction`
- `automorphismConstructibleStage_square_scalar`
- `automorphismConstructibleStage_integral_coherence`
- `automorphismConstructibleStage_integral_shifts`
- `automorphismConstructibleStage_descended_shifts`
- `automorphismConstructibleStage_qbar_linear`
- `automorphismConstructibleStage_inverse_comparisons`

No holes added and no statements split off. The proofs may use existing named
statements whose own proofs are still pending, as required by stage 3.

## No longer needed

Removed direct private imports (their theorems are not invoked by the implemented
proofs; some remain transitively imported by statement interfaces):

- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.Paper.ProEtaleConstantModulePullbackHomology`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.ProEtaleCoefficientModulePullbackComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity`
- `Sheaf.Paper.IntegralAmbientOperationModels`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.CompletedOperationTowerSubstitution`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.IntegralScalarExtensionUniverses`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.Paper.ScalarExtensionExactIntrinsic`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`

No module is withdrawn. The original route remains relevant to the retained
coherence and shift holes; these dependencies are not declared globally pruned.
The unit `sk-prop-sf-open-closed-triangle` and its route are preserved.

## Where the brief, the DAG or earlier work was wrong

The item has 22 separate holes, including normalization and coherence assertions;
the general field-transport theorem handles the equivalence clauses but does not
by itself establish their raw Roos shift normalizations. Likewise the simultaneous
comparison-system existence theorem does not itself assert agreement with every
specified framework scalar map. Those distinct obligations have not been weakened.
No definition or statement repair is included.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
