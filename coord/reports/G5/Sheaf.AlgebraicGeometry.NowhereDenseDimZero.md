## What changed

Proved `AlgebraicGeometry.dim_le_zero_of_isNowhereDense` in
`Sheaf.AlgebraicGeometry.NowhereDenseDimZero`, preserving its exact signature and visibility.
Added the proof-only import `Sheaf.AlgebraicGeometry.NowhereDenseDimensionDrop` and reused its
already proved general dimension-drop theorem. If the ambient dimension is already at most zero,
monotonicity suffices, including the empty case. Otherwise the dimension bound forces dimension
exactly one; the general theorem gives dimension of the image less than one. The existing
zero-dimensional closed-subset theorem then supplies closed image points, and the closed embedding
pulls their closedness back to the subscheme.

Updated only `proof`, `proof_deps`, `proof_origin`, and obsolete entries of `tool_uses` on
`lem-pc-nowhere-dense-dim-zero`. No definition or statement changed and no consumer adaptation is
needed. The unit's own statement and proof route are preserved: its realized records are empty,
and this is a shorter proof of the same subsidiary dimension inference.

Validation: the complete proof compiled cleanly through `lcompile.py` (5.2 seconds).
The import-direction check permits the new proof-only import. Delivery preflight supplies the
independent axiom probe and final compilation.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.dim_le_zero_of_isNowhereDense`
(node `lem-pc-nowhere-dense-dim-zero`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The general dimension-drop theorem, scheme/topological dimension comparison, and
zero-dimensional closed-point theorem used here are already proved.

## No longer needed

No existing import was removed: the four public imports support the existing statement interface,
and `WeilConjectures.Mathlib.Topology.KrullDimension` supplies the embedding/range dimension
identity and zero-dimensional closed-point theorem actually used by the proof.

The explicit component-by-component argument no longer directly needs
`lem-weil-pbc-noetherian-finitely-many-components` or
`lem-sc-irreducible-components-cover`. Their `proof_deps` and obsolete top-level `tool_uses` entries
were removed. The proved general dimension-drop theorem encapsulates the component argument;
its own dependencies remain its responsibility. Neither of these Mathlib leaves has a separate
Sheaf module to withdraw, so no library module is claimed as globally pruned.

`def-pc-dimension` remains a statement dependency, but its definition is not unfolded by the proof:
`lem-pc-scheme-dimension-local-rings` supplies the comparison instead. No other planned dependency
was bypassed. No new intermediate theorem or module was introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The old plan did not reuse the now-proved
`AlgebraicGeometry.Scheme.topologicalKrullDim_lt_of_isNowhereDense`
(node `lem-sc-hilbert-nowhere-dense-dimension-drop`). Its hypotheses fit after deriving local
Noetherianity and separating the ambient dimension-at-most-zero case from dimension exactly one.
The new route also handles empty X and Z without any extra hypothesis.

Searches: the prior interrupted session recorded a LeanFinder search for nowhere-dense dimension
drop. Loogle on `IsNowhereDense` found the topology API but no dimension theorem; the prescribed
grep search found no exact combined theorem. Direct `rg` in `lean/Sheaf` found the proved general
theorem above. Signatures and proofs of all used library declarations were read.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
