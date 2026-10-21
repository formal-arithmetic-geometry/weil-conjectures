## What changed

Restored the complete quarantined Sheaf.Paper.ExceptionalCoefficientComparison module
from its current rework row. Proved tensorIso_existsUnique from the existing canonical
flat-model tensor comparison, extending the equation to all complexes by naturality
along two flat K-flat resolutions. Proved uniqueness by the existing binary uniqueness
result. Proved unitIso_existsUnique from the K-flat unit representative and the ordinary
and localized unit isomorphisms. Proved siteTensorIso_existsUnique by reflexive HEq and
HEq uniqueness.

Added only proved private proof helpers and the generic public
SiteTensorNormalizationAux definition. The latter keeps the same all-complex equation
behind site tensor constants so that specialized kernel comparisons terminate.
Change record: coord/changes/B3-exceptional-coefficient-normalization.md.
Updated the existing main and tensor-definition nodes to record these proofs and the
new definition attachment. No new node, axiom, source-library edit, or target edit.

## Proved and sorry left

Closed three of the four original holes, all attached to
lem-pur-exceptional-coefficient-comparison and def-pur-exceptional-coefficient-tensor-maps:

- AlgebraicGeometry.Etale.ExceptionalCoefficients.tensorIso_existsUnique.
- AlgebraicGeometry.Etale.ExceptionalCoefficients.siteTensorIso_existsUnique.
- AlgebraicGeometry.Etale.ExceptionalCoefficients.unitIso_existsUnique.

Added holes: none. Split off: none. The previously proved compactSupportMap_isIso is
preserved. The sole remaining hole is AlgebraicGeometry.Etale.exceptional_coefficient_comparison
(node lem-pur-exceptional-coefficient-comparison); its statement and complete ten-step
proof docstring are unchanged. This is a partial proof delivery of a module with several
original holes, not a decomposition of its main theorem.

Validation: full module compiled cleanly in 45.1 seconds. A separate probe printed
only propext, Classical.choice and Quot.sound for each of the three proved theorems
(41.9-second clean compile). A probe retaining the quarantined CompactScalarTensorUnitLaw
and its original use of tensorIso_existsUnique.choose and unitIso compiled in 51.9 seconds.

## No longer needed

No node or module is withdrawn or declared obsolete: the remaining main theorem still
needs its recorded proof dependencies and unit route. Its mathematical plan is retained.
The following direct proof-only imports were unused by the proofs in this packet and
removed; this does not assert their nodes are unnecessary to the remaining main theorem:

- WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullback
- Sheaf.AlgebraicGeometry.ConstructibleSurjectivePullback
- Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
- Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
- Sheaf.AlgebraicGeometry.ProperProjectionFormula
- Sheaf.AlgebraicGeometry.SmoothTensorDuality
- Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
- Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
- Sheaf.Paper.KFlatRingedToposPullback
- Sheaf.Paper.RingedExchangeTensorCoherence
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
- WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
- WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

New direct proof imports supply ordinary scalar restriction/tensor comparison, K-flat
acyclicity, the unit localization comparison, exact-right-adjoint representatives, and
the existing binary etale scalar tensor theorem. They add no unproved intermediary here.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean because of quarantine, not because its declarations were
withdrawn. The full archive and all attachments have been retained. The site's HEq
transport is mathematically reflexive, as its docstring says, but the old specialized
predicate exposes enough nested proof data to make the direct term exceed the compile
limit. The generic wrapper repairs that representation without weakening its equation.
The tensor proof needs only the existing flat-model canonical comparison plus naturality
and flat K-flat resolutions; it does not require a new monoidal-extension existence lemma.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
