## What changed

Partial proof delivery for `Sheaf.Paper.AdicOperationDomainsSourceComparison`.
No declaration signature, definition body, or public import changes.

- `unitDomains` now takes the E-domain projections of the existing
  `shiftedTateUnitScalarCoherence`, at `(X,d)` and `(Y,0)` with the identity
  coefficient embedding.
- `sourceFiniteComparison_existsUnique` constructs the componentwise full-subcategory
  lift with `ObjectProperty.isoMk`, proves naturality using `source_naturality`,
  and proves uniqueness by isomorphism, natural-transformation, and full-subcategory
  morphism extensionality.
- `compactSupport_exact` applies the published `PurCompactSupport.comparison_commShift`
  to the specified coefficient change and compactification.

The item node's proof and proof_origin record these three implementations. Its other
proof steps and dependency set remain for the ten unchanged clauses. Unused private
proof imports are removed. Local unused-section-variable warnings for the two direct
projections are suppressed without changing their existing signatures.

## Proved and sorry left

Closed 3 of the original 13 holes; added 0 holes and split off 0 statements.
All declaration names below are in namespace `WeilConjectures.AdicOperationSource`.
Their node is `lem-pur-adic-operation-domains-source-comparison`.

Proved:

- `unitDomains`
- `sourceFiniteComparison_existsUnique`
- `compactSupport_exact`

Unchanged named theorem holes left in the item module:

- `source_preserves`
- `operationDomains`
- `scalar_preserves`
- `scalar_exact`
- `source_naturality`
- `source_exact_linear`
- `source_composition`
- `source_identity`
- `source_at_unit`
- `source_shift`

No new module or hole is introduced. These are proofs from existing stated
results; dependencies of those results may still contain their own holes.

## No longer needed

Removed the following unused private proof imports from this module:

- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.PullbackTorAmplitude`
- `Sheaf.Paper.TwistPreservesFiniteness`
- `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalShift`
- `Sheaf.Paper.IntegralCompactSupportPrescribedReductions`
- `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`
- `Sheaf.Paper.IntegralCtfTriangulated`
- `Sheaf.Paper.OrdinaryCompletedIntegralPullback`
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
- `Sheaf.CategoryTheory.RingedDerivedPullbackLinear`
- `Sheaf.Algebra.Homology.LineUnboundedDerivedTensor`
- `Sheaf.Paper.IntegralLineTensorComparison`
- `Sheaf.Paper.CompactSupportReductionTower`
- `Sheaf.Paper.CompactSupportTotalLimitRealization`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.CategoryTheory.KInjectiveTotalDerivedLinear`
- `Sheaf.CategoryTheory.LinearRightAdjoint`
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
- `Sheaf.Paper.FiniteFreeCoefficientExtension`
- `Sheaf.Paper.FiniteFreeDerivedScalarCalculus`
- `Sheaf.Paper.CompletedScalarShift`
- `Sheaf.Paper.IntegralTwistScalarCoherence`
- `Sheaf.Paper.SfFrameworkThetaShiftCompatibility`
- `Sheaf.Algebra.Homology.TotalTensorSignedCoherence`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`

No DAG node or entire library module is withdrawn or claimed globally unnecessary.
The other ten unproved clauses retain their planned dependencies: removing unused
imports from this partial implementation does not assert that those future proof
steps can be omitted. All existing public imports remain verbatim.

## Where the brief, the DAG or earlier work was wrong

No statement defect was used or repaired. The full-subcategory uniqueness clause
needs only the existing component naturality and elementary extensionality, rather
than additional geometric theory. An attempted direct implementation of
`source_naturality` was not included: its expanded component calculation exceeded
the compile limit and the bounded revision was interrupted by a server temporary
storage failure before Lean started. That theorem remains exactly as received.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
