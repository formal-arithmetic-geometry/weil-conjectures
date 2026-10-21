## What changed

Filled seven theorem bodies in `Sheaf.Paper.ScalarPerfectDualRealization`, preserving every existing declaration signature and definition. The proof imports `Mathlib.Algebra.Category.ModuleCat.Products` and `Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact` privately.

Validation: the final module compiled through `lcompile.py` in 52.0 seconds with exit code 0 and no warnings.

Change record: `coord/changes/scalar-perfect-dual-private-reducibility.md` documents the local irreducibility command on new private helpers required by the static preflight gate. No public API changes.

Updated the existing node proof and proof-origin descriptions to record the additive finite-product construction and explicit natural comparisons; statement, dependencies and Lean attachment are unchanged.

The scalar realization laws follow from the additive sheafification adjunction and sectionwise tensor functor laws. Private, proved unit and finite-product comparisons transport the supplied scalar finite-free retracts to sheaves; the declared finite-retract exactness theorem and existing bounded-exact-term Hom theorem then give the main theorem. Scalar dual coordinates use the unique surviving target factor, with the differential checked against Mathlib's cochain formula. The normalized signed comparison and its naturality follow from the existing evaluation theorem. The bounds follow from zero terms and the surviving Hom factor.

## Proved and sorry left

Closed seven of the original ten theorem holes, with no new holes and no split-off statements:

- `CategoryTheory.ScalarPerfectDual.realizeMap_laws`
- `CategoryTheory.ScalarPerfectDual.dual_coordinates`
- `CategoryTheory.ScalarPerfectDual.scalarPerfectDualRealization`
- `CategoryTheory.ScalarPerfectDual.comparison_existsUnique`
- `CategoryTheory.ScalarPerfectDual.comparison_natural`
- `CategoryTheory.ScalarPerfectDual.ordinary_comparison`
- `CategoryTheory.ScalarPerfectDual.dual_bounds`

Three original theorem holes remain, all attached to `lem-sfb-scalar-perfect-dual-realization`:

- `CategoryTheory.ScalarPerfectDual.evaluation_existsUnique`
- `CategoryTheory.ScalarPerfectDual.evaluation_natural_isIso`
- `CategoryTheory.ScalarPerfectDual.derived_comparison_natural`

This is a partial delivery of the multi-theorem module. The three retained holes are unchanged; no hole was moved or repackaged. The comparison proofs use these declared evaluation results, and the exactness proof uses the declared `ringedSite_finite_retract_dual_exact` dependency. Every added private helper is fully proved.

## No longer needed

None. No imports removed and no node or module withdrawn. The remaining evaluation proofs still need the stated sheafification, tensor and internal-Hom dependencies. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy established. The source `homComplex_to_single_iso` exposes existence but does not pin its components publicly; the unfinished derived naturality proof needs an explicitly normalized natural comparison. Its exploratory construction was not retained in this delivery. No statement or definition repair was needed. The finite-free, coordinate and vanishing arguments include rank zero, zero terms, empty intervals and unbounded ambient complexes; no flatness hypothesis was introduced.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
