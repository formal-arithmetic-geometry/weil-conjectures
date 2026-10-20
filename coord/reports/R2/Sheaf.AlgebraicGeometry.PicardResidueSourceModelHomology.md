## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PicardResidueSourceModelHomology.lean` from its
quarantine copy after the upstream cluster restore. The module contains the complete
proof of `AlgebraicGeometry.Scheme.picard_residue_source_model_homology`; no theorem
statements or imports were changed.

## Proved and sorry left

`picard_residue_source_model_homology` is proved. The restored module contains zero
`sorry`s, and this delivery adds zero `sorry`s.

## No longer needed

None. Every import retained by the restored proof is used by its declarations or proof.
No DAG nodes or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier merge-queue cluster restore removed the module from `lean/` even though
its quarantine copy contained a compiling, complete proof. The DAG statement and proof
plan are unchanged.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
