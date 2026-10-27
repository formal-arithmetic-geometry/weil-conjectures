## What changed

Only `Sheaf.Paper.CompactSupportProjectionFormula` changes on the Lean side.
Two existing theorem holes are filled without changing their signatures:

- `integral_mem` transports the existing exact-pullback preservation theorem across
  `pbcIsoCompletedPullback_identification`. The geometric coefficient hypotheses
  supply isomorphism closure of the integral constructible predicate.
- `cancellation_existsUnique` forgets the actual finite-equivalence counit. The
  supplied `finite_functors` identity identifies its carrier with the rational
  realization; equality transport supplies the required endpoints. Its prescribed
  raw arrow determines the isomorphism uniquely.
The generic fixed-pair carrier helper is private and fully proved. No public
declaration, object construction, target signature or normalization is replaced.

## Proved and sorry left

Original holes: 9. Closed: 2. Added: 0. Split off: 0. Remaining: 7.

Closed declarations (proofs from existing named declarations):

- `WeilConjectures.CompactSupportPbcTransport.integral_mem`.
- `WeilConjectures.CompactSupportPbcTransport.cancellation_existsUnique`.

Remaining named theorem holes, all attached to `fix-prop-projection-formula`:

- `WeilConjectures.compactSupportProjectionFormula`.
- `WeilConjectures.compactSupportProjectionFormula_coefficients`.
- `WeilConjectures.CompactSupportWeilProjection.openMate_isIso`.
- `WeilConjectures.CompactSupportWeilProjection.restriction`.
- `WeilConjectures.CompactSupportPbcTransport.bridge_existsUnique`.
- `WeilConjectures.CompactSupportPbcProjection.forward`.
- `WeilConjectures.CompactSupportPbcProjection.tensor_identification`.

No new theorem hole or definition hole is added. The supplied preservation
theorems and bridge retain their existing proof obligations.
This is a partial proof delivery, not a claim that the whole module or its target
closure is axiom-free.

## No longer needed

Removed unused private proof imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle`.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`.
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`.
- `Sheaf.Paper.CompactificationCoherence`.
- `Sheaf.Paper.ComparisonTorAmplitude`.
- `Sheaf.Paper.CompletedDirectImageLimits`.
- `Sheaf.Paper.DerivedNakayama`.
- `Sheaf.Paper.DerivedPullbackTensorHom`.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`.
- `Sheaf.Paper.FiniteCoefficientTensorCtf`.
- `Sheaf.Paper.FiniteDirectImageComposition`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`.
- `Sheaf.Paper.IntegralResidueTor`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.Paper.PullbackTorAmplitude`.
- `Sheaf.Paper.QcqsCompactSupportRealization`.
- `Sheaf.Paper.RefinementComparisonIsomorphism`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.ScalarExtensionExactIntrinsic`.
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`.
- `Sheaf.Paper.SfRationalizationKaroubi`.
- `Sheaf.Paper.WeilTensorProduct`.
- `Sheaf.SixFunctors.CompositionProjectionMate`.
- `Sheaf.SixFunctors.ConstructibleTensorCompletion`.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`.
- `Sheaf.SixFunctors.ProperOpenProjectionMate`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius`.

These imports are unused by the completed transport proofs and the existing
statements and definitions. Some are already transitively available through the
unchanged public imports. Their removal does not withdraw the finite, adic,
field, coherence or Weil obligations of the six unfinished theorem proofs.
No whole module or DAG node is withdrawn; no source-library declaration is removed.
The unit's finite/reduction/adic/field/site/coherence/Weil route remains in place.

## Where the brief, the DAG or earlier work was wrong

The original transport proofs did not require a new geometric projection theorem:
exact transport preservation, the finite comparison functor identity, and the
actual equivalence counit already suffice for the two completed declarations.

STATEMENT-DISPUTED: the remaining `bridge_existsUnique` has a normalization mismatch in the present
library. `completedFrobenius` is the stage of `pbcQbarPullFamily`, whose defining
formula is `pbcDescentPullback`; this uses `pbcActualCompletedPull`, i.e. ordinary
pullback followed by the intrinsic reflection. In contrast, `integralBridge`
starts at `completedPullbackObject`, the strict quotient-tower construction.
`pbcActualCompletedPullback_tower` supplies a unit-compatible isomorphism from
that strict construction to the reflector construction. The displayed HEq in
`bridge_existsUnique` omits its inverse. HEq of these arrows requires equality
of their source objects; an isomorphism of those objects does not supply that
equality. No source-object equality is part of the reflector specification.
The expected corrected normalization includes the localized inverse tower
comparison before `integralBridge`. This delivery leaves the existing statement
and hole in place and flags the issue; no weaker replacement is proved.

The main all-coefficient laws, coefficient squares, open mate invertibility,
framework Weil restriction, forward coefficient transport, and tensor identification
are not proved here. The attempted generic forward transport exceeded the elaboration
budget when matched to concrete coefficient endpoints and was removed from this packet.
The prescribed dependencies were read; their coordinate transports and coherence
assemblies remain actual obligations, rather than new restatements with holes.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
