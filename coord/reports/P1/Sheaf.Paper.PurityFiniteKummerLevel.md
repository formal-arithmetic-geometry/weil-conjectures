## What changed

The module now contains real proofs of the arithmetic and finite coefficient-basis clauses of
`finiteKummerLevel`. The proof constructs the DVR data, computes the residue rank, proves the
principal ideal and minimal annihilator properties, and constructs the additive `ZMod` basis
with its scalar-linearity equation. The expensive unused root-pullback helper chain was pruned.
The remaining geometric comparison, derived compatibility, and base-change clause is a named
public theorem `finiteKummerLevel_geometric` with its own DAG node and a single `sorry`.

## Proved and sorry left

Proved: `kummerBasisMod`, `kummerDvrData`, `kummerResidueRank`, `kummerArithmetic`,
`kummerCoefficientBasis`, and the arithmetic and coefficient-basis portion of
`finiteKummerLevel`.

Sorry left: `finiteKummerLevel_geometric`, node `lem-pur-finite-kummer-level-geometric`.
The parent theorem is proved from this strictly smaller geometric comparison statement.

## No longer needed

The removed private declarations `kummerRootPullInclusion`, `kummerRootPullTransition`,
`kummerRootLimitPull`, `kummerScalarExt_hom_ext`, `kummerScalarTranspose`,
`kummerScalarTranspose_injective`, `kummerComparison_unique`, `kummerTensorSecondIso`, and
`kummerDerivedOfIso` are no longer needed by the retained proof. Their supporting imports and
planned root/base-change proof route remain represented by the new node's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The original module bundled the arithmetic, normalized sheaf comparison, derived tensor, and
base-change arguments into one theorem. The retained arithmetic proof compiles independently,
but the geometric portion requires a separate statement to keep the module within the file
compile limit and to expose the genuinely separate result. No target statement was changed.

## New nodes

`lem-pur-finite-kummer-level-geometric` records the normalized finite Tate-line comparison,
derived compatibility, and arbitrary base-change square as a separate strictly smaller result.

The import/interface pruning is recorded in `coord/changes/PurityFiniteKummerLevel-pruning.md`.

Change record: `coord/changes/PurityFiniteKummerLevel-pruning.md`.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
