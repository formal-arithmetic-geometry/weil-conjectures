## What changed

Restored `Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofVertexNormalization`
from its complete quarantine archive named in `coord/rework.tsv`.
The public statement and docstring and all six imports are unchanged.
The archived proof constructs denominator isomorphisms and then applies
`relativeMV_resolved_roof_mate_comparisons`.

Removed the redundant local irreducibility entry for `derivedPullback`,
which upstream now declares with `irreducible_def`, and kept
`RingedSpace.moduleDirectImage` folded in the public proof.
Concrete row and functor comparisons are expensive to elaborate. A proved
private generic helper,
`row_roof_vertices_isIso`, composes the three localized vertex isomorphisms
with the vertex components of the row-functor comparison isomorphism.
Passing the three proofs explicitly avoids instance search through concrete
row projections. The second proved private helper,
`combine_vertex_comparisons`, inserts the three denominator witnesses into
the six comparison witnesses returned by the existing mate theorem. It keeps
existential assembly abstract instead of repeatedly comparing their concrete
derived-category types. The public proof reduces statement aliases once with
projection reduction disabled, and binds only the aliases it uses.
No definition, source-library declaration, hypothesis, conclusion or target
changes. The mathematical route is preserved.

Validation: the complete repaired module, with its actual imports, compiled
through `lcompile.py` in 39.7 seconds, exit code 0, with no errors or warnings.
A first delivery compile timed out at the unchanged 60-second limit before
the abstract witness-assembly helper was added. The final file has no
profiling or tracing options. Its public theorem signature matches the
archive verbatim, and every Lean line is at most 100 characters.
The delivery preflight checks the actual module and its axioms before pushing.

Change record:
`coord/changes/D4-relative-mv-resolved-roof-vertex-restoration.md`.
The sole direct consumer found in the library and quarantine archive is
`Sheaf.AlgebraicGeometry.RelativeMVResolvedRowRoofComparisons`. Its archived
application passes the identical arguments to the identical public statement,
so no consumer adaptation is necessary.

## Proved and sorry left

Assigned zero-hole restoration and compilation repair. Holes closed: none
(0 of 0). Holes added: none. Split off: none. Sorries left: none.
`AlgebraicGeometry.relativeMV_resolved_roof_vertex_normalization` and all
ten private helpers are fully proved. No unproved statement or data
construction is introduced.

## No longer needed

No import, module or DAG node is pruned. All six imports and the quarantined
parent dependency are preserved. Removed the redundant local irreducibility
entry, repeated concrete component elaboration, and unused proof-local aliases.

## Where the brief, the DAG or earlier work was wrong

The operative assignment is the zero-hole restoration recorded in
`coord/rework.tsv`, after a cluster restore. There is no current item-specific
return in `coord/returns/D4.md`. Absence of the module from `lean/` is not
withdrawal: its complete archived proof is restored.

Searches of `dag/nodes` and `dag/units` by module, declaration and blueprint tag
find no attachment for
`lem-pc-relative-mv-resolved-roof-vertex-normalization` in this snapshot.
The archived blueprint tag and dependencies are preserved; no replacement
DAG node is invented.

The required `msearch.py` searches ran. Loogle found
`CategoryTheory.IsIso.of_isIso_comp_left`, already used by the proof.
LeanFinder returned generic localization and quasi-isomorphism results;
grep found generic right-derived-unit isomorphism results. Searches of
both library roots found no replacement for this specialized theorem.
The existing route uses the proved direct-image acyclicity and open-image
resolution comparisons. The new helpers are purely categorical and apply
to arbitrary row morphisms and existential witnesses; empty or repeated opens, zero objects and
zero coefficient maps impose no extra assumptions.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
