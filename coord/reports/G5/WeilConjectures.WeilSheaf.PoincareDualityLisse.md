## What changed

Filled the sole theorem proof in
`WeilConjectures.WeilSheaf.PoincareDualityLisse`, preserving its signature,
visibility, existing docstrings, and every public import. Added private proof
imports of `VerdierDualFinite`, `StalkRationalPoint`, and
`ConstantTwistCohomology`, and four proved private helpers.

The proof follows the degreewise-duality argument of the current blueprint:
apply degree `-i` to Verdier exchange, identify the smooth lisse Verdier dual
with the coefficient dual twisted by `d` and shifted by `2d`, and use
`2d-i=j`. On the coefficient point, shifted degree-one t-exact Verdier duality
identifies the resulting cohomology with the ordinary dual of compactly
supported cohomology. Evaluation through this Frobenius-equivariant linear
isomorphism is perfect and Frobenius invariant. No properness, connectedness,
or restriction on the degrees is introduced.

Three helper proofs are reused from the existing private proofs in
`Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse`;
the new fourth helper proves the elementary linear-algebra assembly.
The UpstreamExtra module itself is unchanged and is not imported, avoiding
its import back to the item module.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`.
Added zero holes; no textual `sorry` remains in the delivered module.
Remote single-file compilation passed with no warnings (5.3 seconds).
The proof uses existing statements of Verdier duality and smooth purity whose
own proofs remain separate stage-3 work; it does not claim these dependencies
are axiom-free. No decomposition or new unproved statement is introduced.

## No longer needed

None. Every existing public import is preserved. All three added private imports
are used. No source declaration, module, or DAG node is withdrawn. The generic
finite-coefficient degreewise-pairing modules are unnecessary for this lisse
rational specialization: existing Weil-complex exchange and point-duality
interfaces already implement the derived-isomorphism route. This does not
retire those generic results or their consumers.

## Where the brief, the DAG or earlier work was wrong

No node has this module in its `lean.module` field in the current repository.
The docstring cites the more general blueprint nodes
`thm-pod-degreewise-perfectness-over-a-field` and
`thm-pod-equivariance-of-the-twisted-pairing`; the first is also listed in
`coord/assumed.tsv`. Their generic statements and proof records are therefore
left unchanged. The actual proof implements their lisse specialization using
already stated source-library Verdier duality, not a new assumed pairing.
The unit route (derived duality followed by cohomology of the dual and shift
reindexing) is preserved.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
