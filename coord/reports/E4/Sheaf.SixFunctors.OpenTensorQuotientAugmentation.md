## What changed

The unchanged theorem `WeilConjectures.OpenTensorQuotient.openTensorQuotientAugmentation`
now assembles the compatible context from `completedOpenTensorRepresentatives`, the finite
open constructibility theorem, actual scheme pullback partitions, and two smaller named
remaining obligations. Its proof constructs prime invertibility from the cardinality of
the finite base field, derives Noetherianity of both finite-type schemes, and fills every
field of the existing comparison structure.

The existing interfaces moved to `OpenTensorQuotientData`, publicly reexported
from the original module, to allow importing the independent remaining lemmas without a
cycle. Existing declaration signatures and data are preserved. The degreewise component
proposition is named `ScalarComponents` and the field uses this definitionally identical
predicate, sharing its type during structure elimination. The main theorem's
signature was also compared byte for byte. Local irreducibility bounds expansion of the
sheaf monoidal and p-adic constructions; it changes no public attributes or definitions.

Change record: `coord/changes/E4-open-tensor-quotient-interface.md`.

## Proved and sorry left

This is a decomposition, not a net hole reduction: one old hole is closed and two
strictly smaller holes are added. The item module has zero remaining holes.

Closed: `WeilConjectures.OpenTensorQuotient.openTensorQuotientAugmentation`.
Its private helpers `restrictionPartitions_proof` and `finiteGeometry_proof` are complete.
The former retains scheme-theoretic intersections and every original index, including
empty intersections. The latter applies the published finite interval theorem directly,
using constructibility of each positive reduction from the integral predicate.

Added:

- `WeilConjectures.OpenTensorQuotient.openQuotientModelGeometry`
  (`lem-sf-open-quotient-model-geometry`): identify finite extensions and prove geometric
  preservation with the same quotient intervals for the fixed compatible model.
- `WeilConjectures.OpenTensorQuotient.openQuotientNormalizedCochains`
  (`lem-sf-open-quotient-normalized-cochains`): specialize the existing generic strict
  coefficient and scalar-unit comparisons to that model, including the normalized
  tensor-completion coordinates.

Each remaining proof is exactly `:= by sorry` in its own module, with its source,
complete proof in words and its own DAG node. No definition or private helper contains
sorry. No arbitrary data is chosen from an unproved existence theorem in a definition.
The existing compatible-context witness is eliminated only inside the main theorem.

## No longer needed

The separate existential calls to `integralOpenReductionComparison` and
`openSemilinearTensorModel` are unnecessary in this assembly: the existing compatible
context supplies their data together with `sameOpen`, avoiding independent witnesses
whose agreement would then need proof. Their declarations and their modules stay in the
library and remain dependencies of the compatible-context theorem.

The main proof does not separately choose K-flat resolutions, invoke generic ringed-topos
tensor pullback, or prove strict scalar/tensor equations inline. The compatible context
already includes normalized ordinary representatives; the remaining cochain node retains
the generic coefficient-interchange and scalar-unit theorems for its construction.
None of those generic dependencies is globally claimed to be pruned.

No module is withdrawn. The extracted interface retains the original public imports; the
original plain imports (ExactProductFunctorStrictLimit, SfImmersionCompletedPullbackComparison,
RingedTopoiCanonicalTensorPullbackOfUniverses, KFlatResolutionIndependentCoefficients,
ExtensionByZeroPresheaf, Mathlib Noetherian) were unused by the declarations and are dropped
(reviewer fix). The postponed
independent steps retain their own named proof dependencies.

The original public prerequisite imports remain available through
the data module's public imports. The unit's open-factor route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The module's original seven-step docstring predates the DAG's newer four-step split and
the subsequently published compatible context. Independent existential choices from the
ordinary and complete comparison theorems do not themselves provide `completeAgreement`.
The existing `completedOpenTensorRepresentatives` theorem supplies that compatibility
explicitly and is reused. It is a generic tool for compatible representatives, not a
replacement for the unit's open-factor or finite-reduction argument.

The generic coefficient-interchange and scalar-unit statements use localized ringed-site
models, whereas the item uses the fixed small pro-etale open models, coefficient-linear
finite comparisons and tensor-completion Roos coordinates. Their specialization and
transport are substantial glue, isolated in the cochain obligation rather than treated
as definitional equality or inferred from separate finite derived evaluations.

Sources read: the current blueprint's open-factor paragraph; Stacks
`sites-modules.tex`, `lemma-j-shriek-and-tensor` (0E8I), and
`sites-cohomology.tex`, `lemma-j-shriek-and-tensor` (0GL1); Bhatt--Scholze
Lemma 6.5.8(2),(3), p.50. The new obligations retain their actual normalization,
unbounded signs, every strict quotient transition, and the uniform interval. Edge cases
checked in their proof plans include empty opens, identity immersions, zero complexes,
empty strata, odd and negative homogeneous degrees, and every positive exponent.

## New nodes

`def-sf-open-tensor-quotient-data` owns the existing unchanged structures and constructions
in the extracted data module; it adds no existence theorem or mathematical assumption.

`lem-sf-open-quotient-model-geometry` isolates finite-model identification and preservation
of integral constructibility and every common quotient interval, independently of tensor
augmentations. It uses the existing finite open theorem, completed immersion comparison
and normalized compatible context.

`lem-sf-open-quotient-normalized-cochains` isolates the strict coefficient and scalar-unit
chain computation and its identification with the first Roos coordinates, independently
of geometric preservation and existential choices of open operations. Its dependencies
retain the already stated coefficient-interchange, scalar-unit augmentation, cochain
pullback coherence and normalized tensor-completion lemmas.

Both new theorem nodes have complete proof steps, true edge-case behavior and logged
LeanSearch, Loogle/LeanFinder and Mathlib grep searches. The current blueprint searches
found no duplicate statement.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
