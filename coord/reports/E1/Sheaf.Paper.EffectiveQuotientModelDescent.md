## What changed

Implemented the five assembly proofs in `Sheaf.Paper.EffectiveQuotientModelDescent`, preserving
all original public signatures, definitions, public imports and declaration docstrings.
Added two strict subproblem modules: transported-system normalization (parent steps 1--2),
and uniqueness of the primitive normalized realizations (part of parent step 6).
Each has one named theorem hole, its source and full proof in words, and a new DAG node.
The parent DAG proof now describes the implemented assembly and the actual dependencies.

Ambient effectivity applies the recorded scheme-general reconstruction theorem to the two
normalized systems and uses the existing primitive model existence theorem. Constructibility
uses the two published preservation theorems and isomorphism invariance with the same interval.
Representative descent extracts the normalized localization uniqueness clauses, uses naturality
of the specified maps, and compares Roos models on K-injective replacements. For the final
Roos descent witnesses it takes the specified total limit itself, the inverse fixed comparison,
and the identity: localization faithfulness proves the required uniqueness.
Scalar coherence uses the general scalar-model composition and unit equations on every complex;
ordinary tensor-generator uniqueness identifies their associator and unitor with the prescribed
ones. Simultaneous choices use the recorded Roos normalization theorem and its existing proved
private `roosModel` construction, followed by the primitive models for each map and inclusion.
The choices occur only in a proof of existence, with no new data definitions.

New proof imports besides the two split modules are `SfIntegralConstructibleTriangulated`
for isomorphism invariance and `SystemScalarCoherence` for scalar composition and unit equations.
Private `import all` imports expose the existing proved scalar-package helpers in
`IntegralComparisonSequenceSystems` and the proved `roosModel` helper in
`TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`. All are proof-only imports.
Two proved private generic helpers transport scalar coherence across model equalities before
specialization; this avoids expensive rewriting through concrete chosen derived models.
The chosen scalar, coefficient and total-limit constructions are locally irreducible during
these proofs. Scalar associator and unitor equalities are substituted only in the final
component equations, avoiding a transport of the entire existential context.

Validation: the supported compiler passed without diagnostics. The new modules compiled
in 40.2 and 39.8 seconds; the final clean item module compiled in 43.9 seconds, below
the 60-second limit. All diagnostic options are removed. Delivery preflight is run by
`deliver3.py`. No target signature, source-library declaration or unit route changes.
There are no consumer adaptations.

## Proved and sorry left

Original holes closed (five, at `lem-trf-effective-quotient-model-descent`):

- `WeilConjectures.effectiveQuotientModelDescent`: decomposed through transported normalization
  and assembled with the existing reconstruction and primitive-model declarations.
- `WeilConjectures.effectiveQuotientModelConstructible`: proved from existing preservation
  theorems and isomorphism invariance, with no new subordinate hole for this argument.
- `WeilConjectures.effectiveQuotientModelRepresentativeDescent`: decomposed through primitive
  realization uniqueness; all localization, quasi-isomorphism, naturality and Roos clauses proved.
- `WeilConjectures.effectiveQuotientModelScalarCoherence`: proved from existing scalar-model
  composition and unit normalization, with no new subordinate hole for this argument.
- `WeilConjectures.effectiveQuotientModelsSimultaneous`: proved from existing normalized models.

Two holes added and remaining in the delivery:

- `WeilConjectures.transportedReductionSystems_normalized`, in
  `Sheaf.Paper.TransportedReductionSystemsNormalized`, node
  `lem-trf-transported-reduction-systems-normalized`.
- `WeilConjectures.primitiveQuotientRealizations_unique`, in
  `Sheaf.Paper.PrimitiveQuotientRealizationsUnique`, node
  `lem-trf-primitive-quotient-realizations-unique`.

No original hole remains inside the item module. This is three proofs from existing declarations
and two decompositions, with five original holes closed and two holes added; it does not claim
five independent mathematical proofs or a sorry-free dependency closure. The exact closure
net is the maintainer's pinned-baseline ledger computation.

## No longer needed

Removed the following unused direct proof imports from the item:

- `Sheaf.Paper.CoefficientExtensionReductionModel`.
- `Sheaf.Paper.SystemNormalizedTensorClosure`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.StrictRoosComparison`.

The first three nodes remain needed by the transported-normalization subproblem; their
specialization is now located there. The last two direct proof nodes
`lem-weil-proetale-countable-products-exact` and `lem-weil-strict-roos-comparison` are not used
by the new Roos uniqueness/descent argument: normalization is already part of each input model,
K-injective replacement compares those models, and localization gives the remaining uniqueness.
Their obsolete parent `tool_uses` approvals are removed, preserving the remaining order.
No module is withdrawn or claimed globally pruned. All original public imports stay verbatim.
The primitive scalar transition/triple/unit proofs are not additionally imported or invoked:
the general whole-system scalar-model coherence theorem gives exactly the requested equations.

## Where the brief, the DAG or earlier work was wrong

The primitive comparison dependency already carries `STATEMENT-DISPUTED`, with the detailed
counterexample in `coord/reports/T6/Sheaf.Paper.PrimitiveQuotientRealizationComparisons.md`.
`CoefficientReductionPresentation` fixes the presentation isomorphism only after finite
derived evaluations; conservativity does not imply faithfulness. Its generator normalization
then requires a whole-system limit equation for every presentation isomorphism, including one
twisted by an automorphism invisible at all finite evaluations. The existing T6 report explains
the derived-complete nonseparated p-adic module counterexample.

The ambient existence and simultaneous-existence assertions here inherit that obstruction.
They are explicitly marked `STATEMENT-DISPUTED`, and their existing signatures are preserved.
Their proof bodies are assembly from the existing disputed dependency, not a repair of its
normalization interface. No claim is made that this dependency or its inherited dispute is
resolved. Repairing that shared interface requires a separate reviewed consumer-wide change.
The new primitive uniqueness lemma is conditional on actual normalized models and uses a
single common presentation; it never detects arbitrary derived morphism equality by finite
evaluation. The transported normalization lemma concerns actual system functors only and
contains no primitive universal-presentation normalization.

The old plan's last Roos existence/uniqueness conclusion needs no fresh independent descent
construction: the already specified total-limit functor with the inverse comparison is a
valid witness, and its uniqueness follows from localization.

## New nodes

`lem-trf-transported-reduction-systems-normalized` records only the two normalization steps,
with independent universes and no completeness, counit, unit, primitive realization, or
simultaneous-choice conclusion. It is strictly smaller than ambient effectivity. Its source
is the parent's steps 1--2 (Stacks 07A4, 06YY, 0941), using the existing generic inverse-image
closure and coefficient-extension reduction model; the remaining work is their concrete
sequence-functor specialization and comparison.

`lem-trf-primitive-quotient-realizations-unique` records only the primitive realization
uniqueness part of representative descent. It has no quasi-isomorphism invariance, descended
functor comparison, Roos uniqueness/descent, naturality or counit assertion. The argument fixes
one common good presentation, compares the strict maps on generators and uses good
representatives to extend equality; its source is parent step 6 and Stacks 06YS, 06YY, 0941.

Both nodes keep the parent's chapter and unit, carry the exact Lean statements and record
three kinds of Mathlib search plus the blueprint searches. The required ancestor was
checked with `blueprint_refs.py ancestor`; each new node also gives the exact paragraph
in the current blueprint. No change record is required:
no existing statement or definition is changed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
