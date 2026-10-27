## What changed

Proved `AlgebraicGeometry.Scheme.stratumRlimComparison_isIso` for the specified mate,
using the existing `stratumRestriction_limits` and the new, fully proved helper module
`Sheaf.Paper.ProductPreservingDerivedLimitMate`. The helper extracts the general
normalized Roos / canonical mate argument already present in the descendant
`CompletedOpenEndpointLimitTransport`; importing that descendant would create a cycle.
The helper uses the existing normalized Roos corners, comparison and universal-unit
factorization lemmas. The item identifies its fixed constant comparison with the
inverse identity-component square before applying invertibility.

All existing statements, definitions, attributes and public imports of the item are
unchanged. The only added item import is private. No other existing Lean module changes.
The node's fifth proof step now records the actual argument. The unit route stays.

Validation: the final `lcompile.py --all` run compiled both files without errors or
warnings: 5.0 seconds for the helper and 46.2 seconds for the item. Profiling options
were removed before this final run.

## Proved and sorry left

Closed 1 of the original 4 holes:
`AlgebraicGeometry.Scheme.stratumRlimComparison_isIso`.
Added 0 holes; the new theorem
`AlgebraicGeometry.Scheme.productPreservingDerivedLimitMate_isIso` and every private
helper are proved.

Three original holes remain unchanged, all attached to
`lem-weil-pbc-stratum-completion-unit-restriction`:

- `AlgebraicGeometry.Scheme.stratumModuleReductionIso_exists`.
- `AlgebraicGeometry.Scheme.stratumReduction_normalization`.
- `AlgebraicGeometry.Scheme.stratumReduction_evaluation`.

The result closes a hole, rather than moving one into a new statement.

## No longer needed

No existing item imports removed and no existing module withdrawn or pruned.
The item's direct fifth-step dependencies
`lem-weil-proetale-countable-products-exact` and
`lem-cbc-exact-product-functor-strict-limit` are now used through the new helper and
its existing proved normalization dependencies. They remain mathematically needed;
the new helper has no reduction-tower dependency. The existing dependency
`lem-weil-pbc-reduction-pullback-derived-tower` remains used by other item steps.

## Where the brief, the DAG or earlier work was wrong

No statement or unit-route error found. The plan's inverse-limit step is available
from already proved generic Roos normalization and mate-factorization lemmas.
The closest ready-made mate theorem lives downstream of this item, so its generic
argument must be placed before that dependency cycle. No assumption on Noetherianity
of the restricted scheme is introduced. Identity functors, zero coefficient sheaves
and empty schemes are covered by the categorical proof without exceptional cases.

## New nodes

`lem-weil-pbc-product-preserving-derived-limit-mate` records the proved generic
invertibility of the specified constant-tower / total-derived-limit mate for an exact
module functor with invertible countable product comparisons. Its complete Lean
proof uses normalized Roos models, projection equality and right-derived universal-unit
uniqueness. It has no `sorry`, and does not repeat the completion-unit restriction
statement. No change record is required: no existing public interface changes.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
