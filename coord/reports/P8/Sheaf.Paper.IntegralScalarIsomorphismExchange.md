## What changed

Removed the rejected component extraction and restored `Coherent`, `square`, and
`openInverse` to the item module and its owning DAG node. The item retains the
original `openInverse_isIso` sorry as requested by the reviewer.

## Proved and sorry left

No sorries were closed. The following six declarations retain their original
sorries: `openInverse_isIso`, `integralScalarIsomorphismExchange_integral`,
`integralScalarIsomorphismExchange`, `scalarPull_finiteTor`,
`rectangle_refinement`, and `Systems.strictScalarIsomorphismExchange`.

## No longer needed

The extracted module, component theorem, and associated change record are no
longer needed and were removed.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery split `openInverse_isIso` into a componentwise theorem whose
statement was equivalent to the parent theorem by `NatIso.isIso_of_isIso_app`.
The reviewer correctly required retaining the original single theorem instead.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
