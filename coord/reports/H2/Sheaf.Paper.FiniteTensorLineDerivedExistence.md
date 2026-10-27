## What changed

Added the proof-only import `Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness`.
The original theorem now obtains an existence witness from
`exists_finiteTensorLineDerivedComparison` and proves uniqueness by applying
injectivity of the existing scalar adjunction `homEquiv` and `Iso.ext`.
Added the witness module and its DAG node.

## Proved and sorry left

The original hole in
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorLineDerivedComparison`
is reduced to the strictly simpler existence theorem
`WeilConjectures.PurityFiniteSetting.exists_finiteTensorLineDerivedComparison`.
The latter remains one explicit `sorry`, with node
`lem-pur-finite-tensor-line-derived-existence-witness`.
No definition contains a `sorry` and no existing declaration signature changed.

## No longer needed

No existing imports or proof-dependency nodes were removed. The parent theorem
uses only the witness theorem and the generic adjunction injectivity available
through `finiteTensorAdjunction`; the original detailed local-freeness route is
recorded on the witness node for its next prover.

## Where the brief, the DAG or earlier work was wrong

The original node's existence and uniqueness arguments were bundled together,
although uniqueness is an elementary consequence of adjunction injectivity once
existence is supplied. No statement was found to be false and no unit route was
changed.

## New nodes

`lem-pur-finite-tensor-line-derived-existence-witness` records the strict
existence subproblem and its source-level proof plan. Its Lean declaration is
in `Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness`.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
