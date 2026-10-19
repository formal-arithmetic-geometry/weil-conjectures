## What changed

Proved five rational comparison existence-and-uniqueness theorems by localizing the
corresponding integral isomorphisms. A private proved helper transports isomorphisms
along endpoint equalities and proves uniqueness from the specified heterogeneous
hom equality. The rational pullback and tensor object equations supply those endpoint
equalities. No public statement, definition, or import was changed.

The full module compiled cleanly through lcompile.py (55.2 seconds) before removal
of an unused private helper. Delivery preflight recompiles the final version.

## Proved and sorry left

Closed 5 of the original 24 holes, with no holes added and no new nodes:

- `WeilConjectures.pullbackTensorRationalComposition_existsUnique`
- `WeilConjectures.pullbackTensorRationalAssociator_existsUnique`
- `WeilConjectures.pullbackTensorRationalBraiding_existsUnique`
- `WeilConjectures.pullbackTensorRationalLeftUnitor_existsUnique`
- `WeilConjectures.pullbackTensorRationalRightUnitor_existsUnique`

The following 19 named theorems remain sorry. Each belongs to the existing node
`lem-pur-derived-pullback-tensor-iso` and retains its existing source and proof docstring:

- `WeilConjectures.pullbackTensorCommonComposition_existsUnique`
- `WeilConjectures.pullbackTensorIntegralAssociator_existsUnique`
- `WeilConjectures.pullbackTensorIntegralBraiding_existsUnique`
- `WeilConjectures.pullbackTensorCommonAssociator_existsUnique`
- `WeilConjectures.pullbackTensorCommonBraiding_existsUnique`
- `WeilConjectures.pullbackTensorIntegralUnit_constructible`
- `WeilConjectures.pullbackTensorIntegralUnit_counit`
- `WeilConjectures.pullbackTensorIntegralLeftUnitor_existsUnique`
- `WeilConjectures.pullbackTensorIntegralRightUnitor_existsUnique`
- `WeilConjectures.pullbackTensorRationalScalarUnit_existsUnique`
- `WeilConjectures.pullbackTensorCommonLeftUnitor_existsUnique`
- `WeilConjectures.pullbackTensorCommonRightUnitor_existsUnique`
- `WeilConjectures.canonicalIntegralPullbackTensor_associative_spec`
- `WeilConjectures.canonicalRationalPullbackTensor_associative_spec`
- `WeilConjectures.canonicalCommonStagePullbackTensor_associative_spec`
- `WeilConjectures.canonicalIntegralPullbackTensor_braiding_spec`
- `WeilConjectures.canonicalRationalPullbackTensor_braiding_spec`
- `WeilConjectures.canonicalCommonStagePullbackTensor_braiding_spec`
- `WeilConjectures.derivedPullbackTensorIso`

The integral comparison theorems used by these proofs remain separate existing
obligations. This delivery proves their rational localization steps, without adding
any assumptions or claiming that the integral obligations are closed.

## No longer needed

No imports, modules, or nodes were pruned. The five completed proofs implement the
existing rationalization step of the node's proof plan. The other imports remain for
the unchanged remaining obligations; no new dependency import was added.

## Where the brief, the DAG or earlier work was wrong

No statement or definition error was found. Attempts to lift integral associators and
braidings directly through the reduction/limit adjunction were not completed; their
endpoint transport and reduction-coordinate equalities remain to be checked.
The existing named integral holes were retained. No split-off obligations were added.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
