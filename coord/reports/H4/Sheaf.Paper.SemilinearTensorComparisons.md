## What changed

Proved `WeilConjectures.SemilinearSections.systemTensorComparisons_nonempty` in
`Sheaf.Paper.SemilinearTensorComparisons`. The proof applies the existing
`semilinearTensorEvaluation` at every level and `semilinearScalarTensor` to every
composite coefficient map using the supplied scalar data. It chooses each
comparison with its dependent model, retains the ordinary normalization, and
assembles the five fields. Added only a private proof import of
`Sheaf.Paper.SemilinearScalarTensor`; all existing public imports, declaration
signatures and definitions are preserved.

Updated the attached node's proof, proof dependencies and proof origin to record
this assembly. No existing module or other node is changed. Remote compilation
of the completed item succeeded without warnings in 3.6 seconds. Delivery runs
the required preflight and axiom probe.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.SemilinearSections.systemTensorComparisons_nonempty`
(node `lem-coef-semilinear-tensor-comparisons`). Zero holes remain in the item;
zero holes were added; zero statements were split off. This is a proof from
existing declarations, not a decomposition into new obligations.

## No longer needed

None. No imports, nodes, modules or declarations are removed. Both original
proof dependencies are retained; the existing scalar tensor comparison node is
added as the missing dependency. The unit record has no realized steps or
statement nodes to bypass, and its route is preserved.

## Where the brief, the DAG or earlier work was wrong

The previous single proof step did not cite the existing scalar tensor theorem:
evaluation and scalar coherence alone do not provide the fourth and fifth
fields. The missing node is `lem-coef-semilinear-scalar-tensor`, whose theorem
works for the exact supplied scalar data and level models. Both construction
theorems already exist with complete Lean proofs, so no further split is needed.
The assembly adds no flatness, boundedness or index-strictness hypotheses; the
scalar theorem applies also to equal indices and arbitrary coefficient maps.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
