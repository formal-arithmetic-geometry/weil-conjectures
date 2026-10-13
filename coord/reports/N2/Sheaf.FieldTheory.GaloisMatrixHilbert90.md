## What changed

Added `Sheaf.FieldTheory.GaloisMatrixHilbert90Normalized` and imported it privately. The target theorem now proves the zero-dimensional case directly and reduces the positive-dimensional case to the normalized finite-descent statement.

## Proved and sorry left

`Field.exists_galois_matrix_invariant_basis` is proved by cases on `n`; the `n = 0` case uses subsingleton elimination for the zero-dimensional general-linear group. One sorry remains in `Field.exists_galois_matrix_invariant_basis_normalized`, the positive-dimensional finite Galois invariant-basis argument.

## No longer needed

No existing imports or DAG nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The full finite Galois invariant-basis construction is substantial and was split into the positive-dimensional normalized node; the target's zero-dimensional edge case is independent and is now closed directly.

## New nodes

`lem-sc-galois-matrix-hilbert90-normalized` records the strictly positive-dimensional finite-descent subtheorem left for a subsequent worker.

## Earlier second reading (a previous round; superseded)

Pending the independent second worker review; the target proof compiles and preserves the original statement.

## Second reading by N2

1. Compared the delivered target module with the repository version. The existing theorem signature and all hypotheses and conclusions are byte-for-byte unchanged; only its proof and the private import of the new normalized module differ.

2. Compiled both delivered modules with `lcompile.py --all`. They compile without errors or warnings. The only remaining `sorry` is the explicitly named theorem `Field.exists_galois_matrix_invariant_basis_normalized`; there are no axioms, unsafe declarations, or hollow definitions. A scratch import with `#print axioms` reports only `sorryAx` through that open theorem (and the permitted kernel axioms otherwise).

3. Checked the new split statement against the target and edge cases. It is the target restricted to the genuinely nontrivial positive-dimensional case (`n ≠ 0`); the complementary `n = 0` case is proved directly by subsingleton elimination. The normalized statement is true and has exactly the strength required by the positive branch, with its proof source and node recorded in `lem-sc-galois-matrix-hilbert90-normalized.json`. Searches of the local Lean library and Mathlib found no existing general-linear matrix Hilbert 90 theorem.

4. The proof keeps the unit route: the target still uses the invariant-basis node, and the only pruning is the independently discharged zero-dimensional edge case. No existing imports or proof-dependency nodes became unused.

5. The DAG and Lean agree: the target node records the unchanged declaration and its new proof dependency, while the normalized node records the exact theorem statement, source, proof plan, searches, module, and declaration. The unit `sk-thm-br` remains the recorded unit.

Changed in this second reading: added this review record only; no Lean statements, definitions, or proofs were altered.
