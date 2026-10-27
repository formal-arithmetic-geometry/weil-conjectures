## What changed

In `Sheaf.Paper.AdicPuritySourceReduction`, constructed the finite source comparison
from the recorded intrinsic realization, pullback presentation, finite tensor comparison,
inverse unshifted root diagonal, and shift comparison. Private generic proofs construct the model and identify
any two models by their fixed monoidal structure, functors, objects, and factors.
The concrete theorem opens its normalization predicate explicitly and applies that
construction, identifying the endpoint by unfolding only the purity-arrow wrappers.
All existing signatures, definitions, docstrings and imports are preserved.
The theorem suppresses the unused-section-variable lint locally to retain its existing
scheme-separation binders. The file retains its original elaboration settings.
Updated the existing node's proof description to follow this construction.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.purAdicFiniteSourceIdentification_existsUnique`
(node `def-pur-adic-source-reduction`). No new holes or split statements.
The module has zero remaining `sorry` bodies. Its existing dependency obligations remain
in their original modules; the comparison uses their specified maps.

## No longer needed

None. All three imports remain necessary for the existing statements or Kan-extension proof.
All four recorded proof dependencies are retained. No nodes or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier node left the canonical finite-source normalization postponed. Its existing
factors suffice: their composite has the required endpoint, and the heterogeneous model
specification determines that composite uniquely. No statement repair is required.
The generic argument applies at degree zero, and the finite instantiation uses every
positive exponent n+1; it needs no divisibility or nonempty-scheme hypothesis.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
