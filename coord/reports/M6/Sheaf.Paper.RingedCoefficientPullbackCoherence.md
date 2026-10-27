## What changed

Proved `SheafOfModules.RingedCoefficientProjection.coefficientPullbackCoherence`
in `Sheaf.Paper.RingedCoefficientPullbackCoherence`. All existing signatures and
definitions are unchanged. Added private proved helpers and proof-only imports
of `RingedCoefficientPullbackComparison` and
`SuccessiveDerivedQuotientNormalization`; `import all` makes their existing
private computation and flatness lemmas available.

Ordinary coherence follows from insertion normalization and injectivity of the
composite adjunctions. The derived equations follow on flat-term K-flat
representatives by naturality and the recorded representative equations,
including both equality transports. Naturality and K-flat resolutions extend
them to every derived object. Updated the node's proof and proof dependencies
to record this route. A local irreducibility attribute keeps the final diagram
chase from unfolding the already constructed computation morphism.
No other module is adapted.

## Proved and sorry left

Closed the sole original hole:
`SheafOfModules.RingedCoefficientProjection.coefficientPullbackCoherence`
(node `lem-pur-coefficient-pullback-coherence`). One hole closed, zero holes added,
zero split off. No `sorry` remains in the item or is added elsewhere.

## No longer needed

The direct proof dependency `def-weil-presheaf-modules-sheafification` is removed
from this node: composite-adjunction injectivity supplies the required ordinary
uniqueness. This does not withdraw its module or claim that other proofs no
longer need it. No Lean imports were removed and no modules were withdrawn.
The unit route and the K-flat resolution and pullback dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement was found. The DAG's separate tensor-generation and
sheafification-uniqueness calculation can be replaced by the ordinary
adjunctions already recorded in the interface. No statement or definition
repair, new node, or forced adaptation is required.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
