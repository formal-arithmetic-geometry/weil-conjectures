## What changed

Proved `WeilConjectures.OpenTensorQuotient.openQuotientModelGeometry` in
`Sheaf.SixFunctors.OpenTensorQuotientGeometry`, preserving its complete signature and both
original public imports. Added only private proof imports and proved private helpers.
No other existing Lean module or public interface changes.

The finite comparison comes from `sfFiniteOpenRestriction_presentation` and its
left-adjoint comparison. The context's existing `completeOpen.r` and `completeOpen.s`
compute reductions. A restriction-evaluation isomorphism is assembled from the specified
system equivalence, finite equivalence, and their unit/counit. Exact finite operations
then preserve constructibility and every supplied interval. For restriction, reuse the
proved `pullback_constructible` and `constructible_of_iso` helpers through a proof-only
`import all Sheaf.Paper.FiniteImmersionConstructibilityInterval`; these pull back actual
scheme strata using `proEtale_cartesianStratum_moduleRestriction`.

Updated only the item's DAG node proof, proof dependencies, and proof origin to this route.
The unit statement and its realized proof steps are unchanged. Local instance exclusions
are scoped to individual declarations. No new data is selected from an unproved mere
existence theorem: the finite comparison is uniquely normalized, and all private
comparison data are explicit composites.

## Proved and sorry left

Closed the single original hole in
`WeilConjectures.OpenTensorQuotient.openQuotientModelGeometry`
(node `lem-sf-open-quotient-model-geometry`). One of one holes closed; zero holes added;
zero split-off statements; zero `sorry` left in the delivered Lean module.
The argument introduces no nonempty-open assumption or chosen stratum; it includes empty
opens and the identity immersion, and always uses the positive level `n + 1`.
The proof uses the existing library declarations, with any remaining obligations in
those declarations unchanged. It proves both preservation assertions and both arbitrary
uniform-interval assertions, with the original hypotheses.

Validation: the server delivery compile checked the complete proof in 16.9 seconds
with no hole reported (`SHEAF-PROBED 1`, no `SHEAF-SORRY`). The redundant `hlU` binder
is referenced through a proof-local application without changing its name or signature;
the three overlong
lines reported by that check were wrapped. Final warning-free delivery validation
is recorded by `deliver3.py`.

## No longer needed

No original import was removed and no module is withdrawn. The existing public import
closure is retained. Removed these direct proof-plan edges from the item node:

- `lem-sf-cbc-slice-tensor-generator-coherence` / `Sheaf.CategoryTheory.SliceTensorGeneratorCoherence`:
  tensor-generator coherence is unnecessary for this geometric statement.
- `lem-sf-immersion-completed-pullback-comparison` /
  `Sheaf.Paper.SfImmersionCompletedPullbackComparison`: the context already contains the
  needed reduction square; exact finite restriction suffices.
- `lem-pur-site-restriction-module-adjunction-exact` /
  `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: no direct use of this general
  theorem; the existing finite restriction presentation supplies the specialized
  adjunction comparison. Underlying site constructions remain dependencies of the
  preserved interfaces.

These are removals of direct proof dependencies, not claims that their modules have
become globally unused. No declaration from `WeilConjectures` is removed or changed.
A draft import of `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated` was removed:
constructibility and support transport are proved directly using cohomology isomorphisms.

## Where the brief, the DAG or earlier work was wrong

The plan's completed-immersion pullback comparison and explicit K-flat representative
calculation are stronger machinery than this statement needs. Its supplied compatible
context already records the relevant reduction comparisons and completeness. The newer
finite restriction presentation closes the geometric finite-model comparison directly.
The original explanatory docstring remains as the earlier plan; the DAG now records the
actual shorter proof. There is no false statement, changed definition, target change,
forced adaptation, or new node.

The rework table records an older quarantine path, but the current item source exists.
This delivery preserves and proves that source and its Lean attachment; it does not
withdraw or replace the quarantined obligation with an empty module.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
