## What changed

Added the proof-only module `Sheaf.AlgebraicGeometry.QuasiFiniteDegreeUpperLocusCompactAux`, whose
finite-generation witness theorem isolates the Stacks Tag 07RZ descent argument. The original
module imports it and proves `isCompact_successor_degree_locus_inter_affine` by rewriting with
the compact-open witness. The original theorem signature is unchanged.

## Proved and sorry left

The original `AlgebraicGeometry.Scheme.Hom.isCompact_successor_degree_locus_inter_affine` hole is
closed. The new theorem
`AlgebraicGeometry.Scheme.Hom.exists_compact_open_successor_degree_locus_inter_affine` remains
`sorry` in its own module; it is the finite-generation and descent part of Tag 07RZ.

## No longer needed

The original theorem's direct proof dependencies are no longer imported by its proof; they are
needed by the auxiliary witness theorem. No additional target node is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error or forced adaptation was found. The DAG's single long proof step was decomposed
into a witness theorem and a short set-rewriting proof.

## New nodes

`lem-weil-pbc-qf-degree-successor-affine-compact-aux` is added at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-qf-degree-successor-affine-compact-aux.json` and
stated in `lean/Sheaf/AlgebraicGeometry/QuasiFiniteDegreeUpperLocusCompactAux.lean`.

## Earlier second reading (a previous round; superseded)

Pending the second reader; the auxiliary statement and rewriting proof compile and preserve the original signature.

## Second reading by G1

1. Compared the delivered item module with the repository version. The target theorem's
signature and all existing declarations are byte-for-byte unchanged; only its proof and a
proof-only import changed. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all`. There are no compiler errors,
unsafe features, axioms, or hollow definitions. The target hole is closed; the auxiliary
finite-generation theorem is the one named split-off `sorry`, with its source and proof plan
documented in the declaration and DAG node. Verdict: pass subject to that intentional split.

3. Reviewed the split-off statement and searched the library for an existing declaration.
The existential compact-open witness is a genuine intermediate consequence of Tag 07RZ and
is strictly stronger than the compactness conclusion, so it is not a restatement of the item.
Its hypotheses and conclusion match the intended descent argument. Verdict: pass.

4. The target proof now takes the shortest available route after the finite-generation witness:
rewrite the target set using the witness equality and return its compactness. The original
direct proof dependencies remain needed by the auxiliary theorem; the item's import of the
auxiliary module is private to the proof. No further pruning was available. Verdict: pass.

5. Checked the target and auxiliary DAG records against the Lean declarations. The auxiliary
node records its statement, source, proof dependencies, proof origin, module and declaration;
the target node records the rewritten proof dependency and origin. The unit's realized route
is preserved because the witness theorem is the decomposition of the existing Tag 07RZ step.
Verdict: pass.

Changed report only for this second reading; no Lean statements or definitions were changed.
