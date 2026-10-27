## What changed

Filled `WeilConjectures.integralPullbackStrictFiniteComponent`. Its statement and
`integralComparisonRestrictedEvaluationFactors` are unchanged. The proof first
identifies the ordinary chain maps on inverse-image unit generators, then applies Q
and the exact-functor factorization equations and cancels invertible comparisons.

Added `Sheaf.Paper.IntegralPullbackStrictFiniteGenerators`, containing the completely
proved private generator calculation and its implementation helpers. Profiling the
concrete coefficient constructions led to explicit local functor presentations and
local irreducibility attributes; the generator calculation is compiled separately.
The item imports that implementation with `import all`.
`IntegralPullbackFiniteEvaluationFactors` separately stores the completely proved
exact evaluation calculation on arbitrary finite chain maps. The generator support module imports
`IntegralOperationsWellDefined` for its proved restriction and adjunction helpers.
The evaluation-section transport is proved by generic equality transport, following
the existing proof in `OrdinaryQuotientPullbackTowerComparison`. `MapDerivedCategoryMate` supplies the exact factorization identities.
All local proof attributes preserve the shared definitions and interfaces.

## Proved and sorry left

Closed the one original hole, `WeilConjectures.integralPullbackStrictFiniteComponent`
(node `lem-pod-integral-pullback-strict-finite-component`). No holes added or split off.
No `sorry` remains in the three delivered modules. The support calculation
`WeilConjectures.strictComponent_generators` is proved, as are all its private helpers.
The three delivery modules compile within 60 seconds. The unchanged direct consumers
`IntegralPullbackCounitProjection`, `IntegralPublishedFiniteEvaluation`, and
`IntegralPublishedTowerEvaluation` also compile against this delivery (42, 22, and
28 seconds). Their temporary sandbox copies have been removed. Final proof-import
cleanup is checked by the delivery compile.

## No longer needed

No module is withdrawn. The original public import is retained. Removed the proof
import of `OrdinaryQuotientPullbackTowerComparison`: only elementary equality
transport was needed. Removed redundant direct `MapDerivedCategoryMate` imports
from the item and the evaluation support module; the generator support module
uses that import for the generic exact-square factorization proof.
`def-weil-integral-derived-reduction` is no longer a direct proof dependency: the
needed local surjectivity and restricted inverse-image Hom extensionality are already
proved in `IntegralOperationsWellDefined`, node
`lem-pur-integral-operations-well-defined`. Those proved helpers are used in the new
generator calculation. The remaining original mathematical dependencies are retained
in the item or that calculation.

## Where the brief, the DAG or earlier work was wrong

The planned local-surjectivity step and restricted pullback Hom extensionality were
already implemented as proved helpers; they require no further unproved statement.
The two system presentations agree in the coefficient universes of this statement.
Their explicit unit normalizations suffice, including n = 0, zero complexes, and
empty schemes. No statement repair or shared definition change is needed.

## New nodes

`lem-pod-integral-pullback-strict-finite-generators` records the fully proved ordinary
generator calculation in `IntegralPullbackStrictFiniteGenerators`. Its conclusion is
the equality of ordinary chain maps before the derived localization calculation.
The support module contains no new proof obligation. There are no change records.

`lem-pod-integral-pullback-finite-evaluation-factors` records that exact evaluation
calculation in `IntegralPullbackFiniteEvaluationFactors`, proved from localization
factorization identities and naturality. It adds no hole.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
