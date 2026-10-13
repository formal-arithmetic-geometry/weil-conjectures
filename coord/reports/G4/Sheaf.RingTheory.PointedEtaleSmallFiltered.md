## What changed

Split the conjunction into essential smallness and filteredness intermediate theorems, and proved the target by combining them. Added two DAG nodes for the intermediate obligations.

## Proved and sorry left

`Algebra.pointedEtale_small_filtered` is proved by combining `pointedEtale_essentiallySmall` and `pointedEtale_filtered`.
`Algebra.pointedEtale_essentiallySmall` remains `sorry` (node `lem-sc-pointed-etale-essentially-small`).
`Algebra.pointedEtale_filtered` remains `sorry` (node `lem-sc-pointed-etale-filtered`).

## No longer needed

Removed the proof-only import `Sheaf.RingTheory.StrictHenselizationTriples`; the target proof uses
only the two split declarations. The old target DAG dependencies
`lem-weil-pbc-strict-henselization-triples` and
`lem-weil-pbc-affine-etale-essentially-small-cover` are no longer direct dependencies; they remain
below the split obligations where their eventual proofs require them.

## Where the brief, the DAG or earlier work was wrong

The planned equivalence with residue triples is substantial, so the target was decomposed into its two strictly smaller conjuncts while retaining the exact target statement.

## Second reading by G4

1. Compared the delivered target module with the repository version. The theorem signature and
   all existing declarations are byte-for-byte unchanged; only proof imports and the proof body
   differ.
2. Compiled all three delivered modules with `lcompile.py --all`. They compile successfully. The
   two intermediate declarations are the only remaining named `sorry`s; there are no axioms,
   unsafe declarations, or hollow definitions.
3. Checked the split statements. Each is exactly one conjunct of the target and is therefore true
   at the stated strength, but remains an explicitly sourced obligation rather than a restatement
   used to hide the target proof. The corresponding DAG nodes are present.
4. Checked pruning and dependencies. The target proof uses only
   `pointedEtale_essentiallySmall` and `pointedEtale_filtered`; the unused proof-only
   `StrictHenselizationTriples` import was removed and the report records it.
5. Checked the unit route. The target remains the realization of the same `sk-thm-br` statement;
   the decomposition only supplies its two conjuncts and does not alter the target statement.

Changed the target import list, added this second-reading record, and aligned the target DAG proof
metadata with the two split lemmas used by the Lean proof.

## New nodes

`lem-sc-pointed-etale-essentially-small` and `lem-sc-pointed-etale-filtered` in `dag/nodes/sec-curve-estimates/`, each records the corresponding conjunct and its source argument.

## Earlier second reading (a previous round; superseded)

The target and both intermediate modules compile with `lcompile.py --all`; the target signature is unchanged and each split theorem is a strict conjunct with a source-backed proof obligation.
