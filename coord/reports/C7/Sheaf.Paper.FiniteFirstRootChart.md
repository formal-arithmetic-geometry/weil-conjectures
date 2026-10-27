## What changed

Filled the two theorem proofs in `Sheaf.Paper.FiniteFirstRootChart` without changing
any statement or definition. `finiteTensorPrimeIsUnit` applies the ringed-space
local criterion to `coefficientPrime_isUnit_stalk` already provided by the finite
setting. The first-site comparison uses the published root-normalized site
comparison and inverse realization comparison at the predecessor of the positive
level. Successor injectivity gives its normalization at every level representation,
and that normalization gives uniqueness. An explicit first-line equality avoids
unfolding the intrinsic realization equivalence while matching the two endpoints.

Updated `def-pur-finite-first-root-chart` with these proof steps and their existing
dependencies. No new import or new statement is needed.

## Proved and sorry left

Closed both original holes:

- `WeilConjectures.PurityFiniteSetting.finiteTensorPrimeIsUnit`.
- `WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorFirstSiteLine`.

Both belong to node `def-pur-finite-first-root-chart`. There are zero remaining
holes in the item and zero holes added elsewhere. The proof uses the existing
normalized comparison declarations; their proofs are outside this delivery.

## No longer needed

None. No imports, nodes or modules are withdrawn. All existing public imports
are retained, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The definition node had no proof steps despite the two named proof obligations.
Its record now describes the proofs. No mathematical statement was found false.
A direct elaboration of the transported composite exceeded 60 seconds; profiling
isolated the conversion through `finiteTensorFirstLine`. Explicitly proving its
first-power equality avoided that unfolding, and the full profiled file compiled
in 40.7 seconds. No transparency setting, definition or time limit was changed.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
