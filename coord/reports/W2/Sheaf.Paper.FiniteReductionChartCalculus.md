## What changed

Filled the three theorem proofs in
`lean/Sheaf/Paper/FiniteReductionChartCalculus.lean`.
The shift identity follows by expanding the successor cast and multiplication.
For each normalization theorem, the existing generic isomorphism is the witness:
the published derived tensor is definitionally the native curried tensor.
Reflexive heterogeneous equality proves normalization, and `eq_of_heq` proves
uniqueness. This directly implements the argument already in the docstrings.
All signatures, constructions, attributes, imports and node attachments are retained.
The server single-file compile passed in 33.1 seconds with no diagnostics.

## Proved and sorry left

Closed all 3 of the item's 3 holes, under namespace
`WeilConjectures.PurityFiniteSetting`:

- `finiteReductionPowerShift`.
- `existsUnique_finiteReductionEtaleUnitStep`.
- `existsUnique_finiteReductionTensorUnit`.

No `sorry` remains in the item. No holes or split-off declarations were added.
The declarations remain attached to `def-pur-finite-reduction-chart-calculus`.
These are complete proofs from the existing library constructions; this does not
claim that every dependency of those constructions is already axiom-free.

## No longer needed

None. No imports, nodes or modules were removed. The original node has no proof
dependencies or proof steps to prune. In particular, the pro-etale proof needs no
application of the still-unproved `smoothPurityTensorPresentation`: the equality
of presentations is definitional. Existing public imports retain their reexports.
No new proof imports were necessary.

## Where the brief, the DAG or earlier work was wrong

No statement or definition defect found. The generic maps already have the required
types, so explicit transport across a propositional tensor-presentation identity
is unnecessary. The unit route and the chosen canonical maps are preserved.
The arithmetic proof includes dimension zero; the normalization arguments work for
all shifts and coefficient categories allowed by the original statements, including
the zero ring in the etale specialization.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
