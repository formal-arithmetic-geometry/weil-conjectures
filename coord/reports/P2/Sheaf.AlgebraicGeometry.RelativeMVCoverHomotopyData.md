## What changed

Restored lean/Sheaf/AlgebraicGeometry/RelativeMVCoverHomotopyData.lean from the
quarantine path recorded in coord/rework.tsv and repaired its final overlap-map
calculation. The archived proof reaches the default 200000-heartbeat limit at whnf.
A trace.profiler run places the failure in the final backward rewrite chain,
after dsimp of the cone-to-quotient isomorphisms.

The replacement maps Mathlib's explicit mappingCone.map_descShortComplex P P′ m
equation by congrArg (fun k ↦ DerivedCategory.Q.map k ≫ e₃′.hom), then simplifies
with map_eq_mapOfHomotopy, Functor.map_comp, associativity and the existing
quotient-component equation. This proves the same overlap comparison directly.
The repaired module compiles without warnings through lcompile.py in 10.8 seconds
and again in 7.9 seconds, at the original heartbeat and file-time limits.

The theorem signature was mechanically compared with both the archived signature
and the node's lean.statement: all are identical. Imports, docstrings, visibility,
universes, witnesses and the two proof dependencies are preserved. Updated step 3
and proof_origin of lem-pc-relative-mv-cover-homotopy-data to describe the repaired
calculation. Restoration and consumer inventory are recorded in
coord/changes/P2-relative-mv-cover-homotopy-restoration.md.

## Proved and sorry left

This is a zero-hole rework repair. The archived module has zero direct holes;
the delivered module has zero direct holes. No hole is closed or added and no
statement is split off. AlgebraicGeometry.relativeMV_cover_homotopy_data has a
complete proof from relativeMV_cover_rows and Mathlib. This delivery repairs its
compilation; it does not claim to prove the entire transitive dependency chain.

There are no remaining sorry declarations in the delivered module, no new
modules, no private holes and no data definitions changed.

## No longer needed

None. All three imports remain needed: RelativeMVMaps supplies the public
statement; RelativeMVCoverRows supplies the resolved cover rows; Mathlib's
HomotopyCategory.ShortExact supplies the cone quasi-isomorphism and naturality.
The node retains lem-pc-relative-mv-cover-rows and
lem-pc-cone-short-exact-quasi-iso. No module or node is withdrawn or globally
pruned, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The rework row records a global-build failure without a compiler diagnostic.
Compiling the archived source reproduced a deterministic heartbeat failure in
the final rewrite chain, not a missing mathematical hypothesis. Profiling then
identified that chain as the source of the failure. An explicit congrArg and
forward simplification repair it without changing definitions or raising limits.

The archive and DAG attachment are preserved: absence from lean/ does not mean
the item was withdrawn. tools/downstream.py --allow-missing reports zero current
library consumers, while a search of quarantine finds the unchanged
StandardSingleUnionHomotopyChainData consumer and its DAG parent still cites
this theorem. It therefore remains needed.

Mathlib searches using leanfinder, loogle and grep found map_descShortComplex
and quasiIso_descShortComplex as the direct algebraic tools already used by the
proof; no new geometric result or split is required.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
