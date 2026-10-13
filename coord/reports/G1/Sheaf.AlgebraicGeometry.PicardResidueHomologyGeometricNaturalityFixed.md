## What changed
Added a positive-cardinality intermediate theorem carrying the geometric naturality argument as a split obligation. The main theorem handles the empty family directly and delegates the positive case.

## Proved and sorry left
The empty-family case of `picard_residue_homology_geometric_naturality_fixed` is proved. `picard_residue_homology_geometric_naturality_fixed_positive` remains `sorry` and is the nonempty-family geometric comparison obligation.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The DAG's one-step proof plan does not provide a formal derived-category construction for the required arrows; the positive-family argument remains an explicit split theorem.

## New nodes
new-picard-residue-homology-naturality-fixed-positive records the positive-cardinality split obligation, with the exact Lean signature, proof route, source, and three searches.

## Second reading by G1

1. I compared the delivered module with the repository version. The existing target signature is unchanged; the only added declaration is the explicitly split positive-cardinality theorem.
2. I compiled the module with the launcher. It compiles cleanly after correcting the argument shadowing and formatting the long application; the remaining `sorry` is exactly the named split theorem, with no forbidden declarations or hollow definitions.
3. The split statement is a true restriction of the target to `0 < n`, and its docstring records the geometric comparison argument and source tags. Its DAG node is included in this delivery.
4. The proof follows the target's route: the empty finite family is discharged by `Fin.elim0`, while the positive case delegates to the restricted theorem. No unit step is bypassed and no imports were removed.
5. The DAG node and Lean declaration agree on the split theorem and its module; the target node's statement and dependencies are unchanged.

I changed the positive-case call to pass the original kernel equality hypothesis (the previous local name shadowed it with the positivity proof), shortened the application to satisfy the line-length check, added the missing DAG node file, and appended this review.

