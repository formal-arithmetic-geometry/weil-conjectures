## What changed

Replaced the hole in `WeilConjectures.rationalTensorAssociator_scalar_square`
with a complete reduction to the integral scalar square, in the new module
`Sheaf.Paper.IntegralTensorAssociatorScalarSquare`.

The naturality clause uses `pullbackTensorIntegralAssociator_naturality` and
three tensor-product inductions. On pure tensors, the prescribed rational tensor
formulas and associator component formula reduce it to integral naturality;
the coefficients agree by associativity of multiplication. The zero and addition
cases use the actual bilinear Hom maps.

For scalar compatibility, the rational tensor and scalar-extension object formulas
identify all endpoints. The associator and scalar-comparison component formulas,
the scalar map formula at coefficient one, and the tensor map formula at two
coefficients one identify each factor with its localized integral counterpart.
The proof composes these heterogeneous equalities, applies localization to the
integral scalar square, and reflects the resulting heterogeneous equality to the
required ordinary equality. All rational objects are covered because rational
localization retains integral objects.

Validation: the new integral module compiled in 1.3 seconds, and the assigned
module compiled without warnings in 21.7 seconds using `lcompile.py`.

Only the assigned module, its node, the new integral module and its node change.
Existing signatures, definitions, instances, attributes and public imports stay as
before. The new theorem states the integral step of the original node's proof,
without rational naturality or rational compatibility. This is a decomposition,
not a net reduction in holes.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.rationalTensorAssociator_scalar_square`
(node `lem-pur-rational-tensor-associator-scalar-square`) by a complete Lean
reduction. The naturality clause is proved from the existing integral naturality
lemma. The scalar clause is proved from the new integral square.

Added one hole:
`WeilConjectures.integralTensorAssociator_scalar_square`
(node `stage3-pur-integral-tensor-associator-scalar-square`, module
`Sheaf.Paper.IntegralTensorAssociatorScalarSquare`). Its proof is exactly
`by sorry`; its docstring and node give the complete reduction/counit pasting
argument from the original integral Step 1.

Original holes: 1. Holes closed: 1. Holes added: 1. Holes remaining in the
assigned module: 0. Holes remaining in the delivery: 1. Net: 0 (decomposition).

## No longer needed

No original public import is removed. The proof imports only the integral
naturality theorem and the new integral square, together with private proof
helpers of the already imported constraint module. The existing rational
naturality theorem was considered but is not imported: its DAG dependencies
reach this item through the common-associator existence theorem.

The following old dependencies are no longer needed directly by the assigned
module; they remain needed by the new integral-square subproblem and are not
claimed as globally pruned:

- `lem-trf-ambient-comparison-system-existence`
- `lem-trf-primitive-quotient-scalar-model-existence`
- `stage3-pur-scalar-tensor-model-normalization`
- `lem-pur-integral-scalar-reduction-intertwining`
- `stage3-pur-scalar-tensor-limit-square`
- `lem-pur-scalar-extension-tower-coherence`
- `lem-pur-system-scalar-associator-coherence`
- `lem-pod-integral-system-reduction-fully-faithful`

The item's obsolete `tool_uses` entries for
`lem-pod-integral-system-reduction-fully-faithful`,
`lem-trf-ambient-comparison-system-existence`, and
`lem-trf-primitive-quotient-scalar-model-existence` are removed. The defining
integral constraints remain a direct dependency and retain their existing approval;
the other three tools now belong to the deferred integral argument. No Lean module is
withdrawn, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assignment opens despite two of its current proof dependencies having no
Lean attachment, both in the shared snapshot and in the current server records:
`lem-pur-integral-scalar-reduction-intertwining` and
`lem-pur-system-scalar-associator-coherence`. Accordingly the complete original
integral Step 1 cannot yet be implemented by applying all of its named Lean
statements. The delivery isolates precisely that integral step, while carrying
out both rational arguments in Lean.

The existing rational naturality declaration has an acyclic Lean import path,
but its DAG statement dependencies reach the assigned item through
`lem-pur-derived-pullback-tensor-constraints` and
`lem-pur-derived-pullback-tensor-constraints-common-associator-existence`.
The delivery avoids that DAG cycle by using the stated integral naturality lemma
and making the localization induction explicit.

Stacks 07A4 supplies the K-flat tensor comparison, not the entire completed
scalar-associator assertion. The new node honestly keeps the original agent
expansion and its normalization dependencies. The reviewed warning about pinning
the system associator to its K-flat normalization remains relevant to the missing
system-coherence dependency; this delivery introduces no arbitrary monoidal
structure and changes none of the prescribed maps.

## New nodes

`stage3-pur-integral-tensor-associator-scalar-square` states only the completed
integral scalar-associator square. It is strictly an earlier step: the assigned
rational naturality proof and the complete localization of the scalar square are
proved in the parent. Its proof is the integral part of Step 1 of the existing
node, with the separate integral-naturality clause removed. Searches in the DAG,
current blueprint, Lean source library and Mathlib found no existing statement of
this exact integral square. The three Mathlib search kinds are recorded from
`msearch.py`. Identity coefficients, zero inputs, empty schemes and ramified
extensions use exactly the same normalized reduction and counit equations; no
extra hypothesis excludes any of those cases. There is no change record because
no existing statement, definition, module interface, or other node is changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralTensorAssociatorScalarSquare": "5229c94c8b42ab63cabb27f60af96f4a6eb8c77e", "Sheaf.Paper.RationalTensorAssociatorScalarSquare": "8f22e7f7e8d5d8c6cbabd5949a22919307a1c9af"}, "results": {}, "time": "2026-10-28T14:47:32+0800", "transitive": 0, "version": 1}
```

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
