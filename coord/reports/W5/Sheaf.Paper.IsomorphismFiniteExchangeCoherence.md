## What changed

In `Sheaf.Paper.IsomorphismFiniteExchangeCoherence`, implemented the two coefficient-factor
clauses `WeilConjectures.FiniteExchangeCoherence.properCoefficient` and
`WeilConjectures.FiniteExchangeCoherence.openCoefficient`.

The proof first identifies the prescribed `scalarPull` with the inverse scalar-adjunction
mate of the canonical restriction/pullback square, using conjugate mates and uniqueness of
left adjoints. The existing `scalarTensorPullbackSquare` then supplies the actual coefficient
cube for the quotient map. The proper clause applies `coefficient_exchange_of_counit` with
the existing coefficient mate equations. The open clause derives the inverse coefficient
map's open-unit normalization from `scalar_open_normalized`, rotates the same cube, applies
`openScalar_exchange_of_unit`, and identifies the forward composites by their inverses.
All auxiliary lemmas are private and completely proved.

Added proof imports of `Sheaf.Paper.FourCorners`,
`Sheaf.SecSmoothPurity.ConstantScalarPullbackSquare`,
`Sheaf.Paper.BasicOperationCoefficientCoherence`,
`Sheaf.CategoryTheory.Adjunction.CoefficientExchange`, and
`Sheaf.CategoryTheory.OpenScalarExchangeMate`. Updated the item's DAG proof steps 5 and 6
and their dependency union to describe these arguments. Existing public signatures,
definitions, public imports, and the other completed proofs are preserved.

The large coefficient constructions remain abstract during the two final applications:
local irreducibility attributes and respectTransparency prevent unnecessary unfolding.
The source and target ideals of the small quotient map are specified explicitly.

Validation: the completed proof compiled on the server in 33.6 seconds in the profiling
run. Temporary profiling options were then removed for delivery; the delivery tool
validates the final file again. Static checks found no line over 100 characters, and
confirmed that all existing declaration headers, docstrings and public imports are
preserved.

## Proved and sorry left

Closed two of the three original holes:

- `WeilConjectures.FiniteExchangeCoherence.properCoefficient`.
- `WeilConjectures.FiniteExchangeCoherence.openCoefficient`.

One original hole remains untouched:

- `WeilConjectures.FiniteExchangeCoherence.vertical`, node
  `lem-pur-isomorphism-finite-exchange-coherence`.

Added no holes, public declarations, modules, or nodes. The existing imported statements
may themselves contain sorry, as permitted by the stage-3 dependency contract. In
particular the proper normalization uses the existing
`WeilConjectures.basicOperationCoefficientCoherence`, and inversion of the open coefficient
maps uses the existing `WeilConjectures.PurCompactSupport.openComparison_isIso`.
This is a partial delivery for a module with several original holes, not a decomposition.

## No longer needed

No existing imports were removed and no module was withdrawn. The planned direct use of
`lem-sfb-ringed-derived-monoidal-comparisons` is replaced by the already specified concrete
cube `lem-sp-scalar-tensor-pullback-square`. The planned direct application of
`lem-sf-open-tensor-normalization` is replaced by the existing scalar/open normalization
from `lem-cbc-tower-mate-evaluation-scalars` and the proved categorical
`lem-pur-open-scalar-exchange-unit-mates`. These are changes to this node's immediate proof
route; neither older dependency is withdrawn globally, and the coefficient-coherence
subtree still needs its own open-tensor normalization.

No dependency of the unfinished vertical clause or of the retained existing proofs is
pruned. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The planned general coherence arguments
have a concrete interface already in the library, but identifying it with the exact
`scalarPull` and `openComparison` definitions requires adjunction-mate calculations.
The first conjunct of `basicOperationCoefficientCoherence` is universal in coefficient
systems and scheme morphisms; specializing its auxiliary schemes to the empty scheme
supplies that interface without imposing any extra condition on the schemes in the item.

The existing ordinary vertical transport lemma is not a direct proof of `vertical`:
comparison compatibility with the proper/open composition maps and their compositors
would still have to be established. The original vertical proof and its dependencies are
retained for that work.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
