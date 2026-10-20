## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PicardAffineProjectiveBaseChange.lean` from the
quarantine archive named by the current `coord/rework.tsv` row. The theorem
`AlgebraicGeometry.Scheme.picard_affine_projective_base_change` is retained verbatim,
including its complete proof, private helper theorems, public imports, statement,
and blueprint docstring. The only repair is the proof-only import of
`WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`: the corresponding
`Sheaf.AlgebraicGeometry` compatibility module is now a withdrawn declaration-free stub,
while the existing source module exports the required `derivedPullback_tilde_kFlat_natIso`.

The restored item compiles cleanly with `lcompile.py` in 39 seconds. Its proof uses the
transport theorem, canonical flat-invertible base change, the canonical single-pullback
comparison, the structure-sheaf pullback comparison, and the affine K-flat pullback
comparison. The current DAG dependency already records the affine comparison under its
`WeilConjectures` module, so no node metadata change is needed. The Mathlib searches
found only generic flatness and scalar-extension results; the exact comparison is the
existing source declaration used by the proof.

## Proved and sorry left

This is a rework restoration with zero holes in the assigned module before and after the
repair. No `sorry` was closed, and no `sorry` was added. The restored theorem is already
fully proved by the archived argument; no definition contains `sorry`.

## No longer needed

No import used by the proof was removed. The retired proof-only import
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` is replaced by its existing
source twin `WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`, because
the former has no declarations after the repository's duplicate-retirement pass. No
DAG node or unit route is pruned; the item node's proof dependencies already name the
source comparison node and remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The quarantine archive was correct, but its proof import referred to the retired Sheaf
copy of the affine K-flat comparison. The current node's `lean` record points to the
adopted `WeilConjectures` source module, so the archive's import and the DAG record had
diverged after the duplicate retirement. Updating that private import restores the
recorded dependency without changing any theorem statement or proof argument.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
