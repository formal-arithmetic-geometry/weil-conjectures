## What changed

`Sheaf.Paper.ExceptionalRingTransportCorePostData` now proves
`exists_exceptional_transport_post_data` by assembling the transported functor/comparison
package and the integral-left comparison.  The proof-only import
`Sheaf.Paper.ExceptionalRingTransportCorePostFunctorData` supplies the two split-off
existence statements.  The public reconstruction import remains because the item’s
structure and theorem signatures use `Reconstruction`.

The new module
`Sheaf.Paper.ExceptionalRingTransportCorePostFunctorData` defines the strictly smaller
`TransportCorePostFunctorData` package (all post-data fields except `integralLeft`) and
states the strict-system/reconstruction existence theorem together with the one-field
integral-left existence theorem.

## Proved and sorry left

Closed the item theorem `exists_exceptional_transport_post_data` (one original sorry).
The delivery adds two strictly smaller, named proof obligations:

- `exists_exceptional_transport_post_functor_data`, node
  `new-lem-sf-exceptional-ring-transport-post-functor-data`;
- `exists_exceptional_transport_integral_left`, node
  `new-lem-sf-exceptional-ring-transport-integral-left`.

The item module contains zero `sorry`s.  The two split-off theorems retain one `sorry`
each, with their sources and proof plans in their docstrings and DAG nodes.

## No longer needed

No imports or existing DAG dependencies were pruned.  The item’s public
`ExceptionalRingTransportCoreReconstruction` import is still required by its public
signatures; the split module’s public import is proof-only in the item.

## Where the brief, the DAG or earlier work was wrong

The original DAG step bundled the strict-system transport, reconstruction conjugation,
finite evaluations, and integral realization into one theorem, but no existing Lean
declaration exposed that entire package.  The delivery therefore follows the same route
while splitting it into the functor/comparison package and the independent integral-left
field, both strictly simpler than the item theorem.  No target statement or definition
was changed.

## New nodes

- `new-lem-sf-exceptional-ring-transport-post-functor-data`: the transported functor,
adjunction, reconstruction-comparison, and finite-evaluation fields, excluding
`integralLeft`; Lean module
`lean/Sheaf/Paper/ExceptionalRingTransportCorePostFunctorData.lean`.
- `new-lem-sf-exceptional-ring-transport-integral-left`: the family of integral-left
comparison isomorphisms; Lean declaration in
`lean/Sheaf/Paper/ExceptionalRingTransportCorePostFunctorData.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingTransportCorePostData": "67d70145abf660cd486fa5d40853b7e303ede8fb", "Sheaf.Paper.ExceptionalRingTransportCorePostFunctorData": "40a3e1a0e4980e3795a58d90e0b8352302b376cd"}, "results": {}, "time": "2026-10-28T08:10:01+0800", "transitive": 0, "version": 1}
```

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
