## What changed

Prove `WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorSemilinearReduction`
without changing its statement. Add a private proof import of
`Sheaf.Paper.SignedLineScalarTensorTower` and proved private helpers.
The degree-one comparison is scalar-extension reassociation for the actual
integral quotient maps. Apply the existing signed-line comparison theorem,
then compose its maps with the scalar-extension embedding. Its unit, tensor,
and evaluation formulas give the required normalization.

For uniqueness, use scalar-extension generation in degree one and tensor
generation inductively in positive degrees. In negative degrees, transpose
both maps along extension of scalars and precompose the resulting duals by
the positive comparison isomorphism. Evaluation on pure tensors detects
equality; cancel the dual comparison and recover equality of the original
semilinear maps. This avoids making additional local basis choices.

## Proved and sorry left

Closed: `WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorSemilinearReduction`
(node `lem-pur-finite-tensor-semilinear-reduction`). One original hole closed;
zero holes added; no `sorry` remains in the delivered module.
The full module compiled cleanly through `lcompile.py` in 55.8 seconds.

## No longer needed

None. The existing finite tensor reduction data, coefficient twists,
locally free line theorem and signed scalar comparison remain needed.
No public import, node, module or unit route is removed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The local-basis uniqueness argument in
the plan can be replaced by the existing scalar-extension evaluation
extensionality theorem together with the positive comparison isomorphisms.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
