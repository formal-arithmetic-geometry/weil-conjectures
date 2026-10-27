## What changed

Replaced the proof hole of
`WeilConjectures.purAdicFiniteSourceNormalization_existsUnique` in
`Sheaf.Paper.AdicPuritySourceFiniteness` with the actual prescribed composite.
The witness is `finiteReductionSourceComparison.hom` followed by
`compositionShiftedPullback.map` of `purAdicQuotientNormalization`.
The predicate equations identify the two factors of any other witness with
these fixed factors, and its last heterogeneous equality gives equality of arrows.
The declaration-local unused-section-variable linter is disabled to retain the
existing separation binders unchanged; the proof needs no additional separation
argument. This option affects diagnostics only.
All signatures, definitions, attributes, and imports are unchanged.

## Proved and sorry left

Closed: `WeilConjectures.purAdicFiniteSourceNormalization_existsUnique`
(node `def-pur-adic-finite-source-normalization`, also attached to
`lem-pur-adic-source-finiteness-reductions`). This is a complete proof with no new holes.

Remaining, unchanged: `WeilConjectures.purAdicSource_finiteness_reductions`
(node `lem-pur-adic-source-finiteness-reductions`). Its entire existing named theorem
proof remains `by sorry`, with the source and eight-step proof in its docstring.

Original holes: 2. Closed: 1. Remaining: 1. Added: 0. Split off: 0.

## No longer needed

None. No imports, nodes, modules, or dependencies were removed. The remaining
finiteness theorem still has its existing proof plan and dependency imports.
The closed uniqueness argument needs only the already published canonical factors,
heterogeneous equality, and the category composition already in its statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was needed. The displayed finite-source
endpoints are definitionally those of the root-normalized composite, as the existing
docstring asserts. The existence-and-uniqueness hole therefore needs no new
geometric, tensor, finiteness, or reduction-coherence lemma. The proof works for
equal indices, dimension zero, and empty schemes without extra assumptions.

The current latest blueprint retains the transport unit but no longer contains
the old `thm-pur-adic-reconstruction.proof.md` at the historical path cited by this
node. The existing expanded proof in the node/docstring was used for orientation;
this delivery proves only the endpoint/composite uniqueness step.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
