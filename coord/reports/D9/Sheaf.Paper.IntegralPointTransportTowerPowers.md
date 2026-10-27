## What changed

In `Sheaf.Paper.IntegralPointTransportTowerPowers`, filled the proofs of
`IntegralPointTransportTower.integralSigma_existsUnique` and
`IntegralPointTransportTower.ordinaryEvaluationComparison_existsUnique`.

The integral proof constructs the restriction map as a linear map in each degree,
uses presheaf naturality for its chain-map equation, and proves uniqueness by
extensionality on sections. Private helpers identify the two existing canonical
constant-to-completed coefficient maps by their quotient projections and use the
already proved automorphism scalar normalization. This works also for power zero
and requires no extra hypothesis on the complex.

The finite evaluation proof uses the inverse of the existing generator-normalized
adjunction mate from `OrdinaryQuotientPullbackTowerComparison`. Uniqueness follows
from injectivity of the finite pullback adjunction's hom-set equivalence, after
precomposition with that mate. It applies to arbitrary systems and every level.

Added private proof imports of the two modules with `import all` to reuse their
proved private normalization lemmas. Updated the item's theorem node with these
two subproofs and their dependencies. Existing public signatures, definitions,
instances, attributes, public imports, and docstrings are unchanged.

Validation: the delivered module compiled on the project server in 49.1 seconds
with exit code zero, below the 60-second limit.

## Proved and sorry left

Closed two of the item's original seven holes, with no holes added or split off:

- `WeilConjectures.IntegralPointTransportTower.integralSigma_existsUnique`.
- `WeilConjectures.IntegralPointTransportTower.ordinaryEvaluationComparison_existsUnique`.

Five holes remain unchanged, all recorded under
`lem-trf-integral-point-transport-tower-powers`:

- `WeilConjectures.IntegralPointTransportTower.ordinaryTransport_existsUnique`.
- `WeilConjectures.IntegralPointTransportTower.restrictionComparison_existsUnique`.
- `WeilConjectures.IntegralPointTransportTower.inverseLimitComparison_existsUnique`.
- `WeilConjectures.IntegralPointTransportTower.sectionsLimitComparison_existsUnique`.
- `WeilConjectures.integralPointTransportTowerPowers`.

This is a partial proof delivery, not a proof of the remaining whole-system laws.
No new theorem with `sorry`, axiom, or definition repair is included.

## No longer needed

None. No existing import, module, or DAG dependency was removed. The remaining
whole-system assembly still needs its recorded descent, power, Roos, completion,
and compositor dependencies. The finite evaluation comparison module was already
in the original import closure. The added automorphism restriction module has no
`sorry`, and all its own dependencies were already in that closure.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The reusable scalar normalization
uses the universe-general constant-to-completion construction, whereas this item's
point-sections functor uses the equal-universe construction. Their equality needs
a proof using all quotient projections; treating them as definitionally equal did
not work. The proof supplies that equality without changing either construction.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
