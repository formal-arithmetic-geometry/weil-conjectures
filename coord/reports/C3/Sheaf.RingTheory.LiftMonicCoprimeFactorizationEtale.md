## What changed

Added an auxiliary module splitting the target proof into a core étale factorization
construction and a final reduction compatibility lemma. The target now combines these
statements by a complete Lean proof.

## Proved and sorry left

The target declaration `Polynomial.exists_etale_lift_monic_coprime_factorization` is
proved from the two auxiliary declarations. The auxiliary declarations
`Polynomial.exists_etale_lift_monic_coprime_factorization_core` and
`Polynomial.lift_monic_coprime_factorization_h_reduction` remain sorry-backed nodes.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The six-step construction is too large to elaborate directly within this delivery; it
was decomposed into the universal neighborhood construction and the coefficient
reduction compatibility step.

## New nodes

`lem-weil-pbc-lift-monic-coprime-factorization-etale-core` records the universal étale
construction. `lem-weil-pbc-lift-monic-coprime-factorization-etale-h-reduction` records
the coefficientwise second-factor reduction.

## Earlier second reading (a previous round; superseded)

The target module compiles. The two auxiliary declarations are strictly smaller
components of the target: the core omits the second reduction, while the compatibility
lemma only establishes that omitted equality under the constructed factorization.

## Second reading by C3

1. Compared the delivered target module against the repository version. The target statement is byte-for-byte unchanged; only its proof import and invocation changed.
2. Compiled both delivered modules with `lcompile.py --all`; they compile. The target proof has no new `sorry`; the two named auxiliary declarations remain the report's split-off holes. No forbidden declarations or hollow definitions were introduced.
3. Reviewed the split-off statements. The core is a strict intermediate existential. The reduction lemma was false as delivered: it lacked the reduced factorization and monicity needed for cancellation. I repaired it by adding `hg₀` and `hfactor₀`, and recorded the counterexample and change.
4. The proof route and unit route remain the universal étale construction followed by reduction compatibility; no imports were pruned.
5. Updated the reduction node's Lean statement metadata to match the repaired declaration.

Changed: repaired `Polynomial.lift_monic_coprime_factorization_h_reduction`, updated the target invocation, DAG metadata, and added `coord/changes/lift_monic_coprime_factorization_h_reduction.md`.
