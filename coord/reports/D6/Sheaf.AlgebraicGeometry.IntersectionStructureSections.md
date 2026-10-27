## What changed

Proved `AlgebraicGeometry.Scheme.sections_intersection_structure_colimit` in
`Sheaf.AlgebraicGeometry.IntersectionStructureSections`. The public definitions and theorem
statement retain their meaning. The remaining local supporting lemmas are private and
proved in this module.

The proof applies the declared spectral-presentation and fixed-sheaf continuity theorems,
identifies the restriction maps by their unit equations, and transfers from sets to rings.
Directed-ring cocone recognition supplies all three colimits. The sheaf transport and its
uniqueness follow directly from the inverse-image adjunction, with the restriction squares
proved by naturality. Proof-only imports expose none of this machinery to consumers.

Updated the node's proof, proof dependencies and proof origin to describe this implementation.
The already approved set inverse-image composition tool is explicitly listed as a dependency.
No mathematical statement, definition body, unit route or source-library declaration changes.

Repair of returned head d48e72436bf: removed the duplicate local `compUnit`,
`compUnit_unit`, `compUnit_unique`, `compUnit_comp`, `compMap` and `compMap_heq`.
The existing spectral module now exposes its `compUnit`, `compUnit_unit`, `compUnit_comp`,
`compMap` and `compMap_heq`, and this proof uses them. The existing uniqueness lemma remains
private. No proof or body in the spectral module is changed. The module is unclaimed.
Change record: `coord/changes/D6-spectral-comparison-api.md`.

Validation: both modified modules compiled cleanly through `lcompile.py` (21.0 and 34.3 s).
The unchanged direct consumers `IntersectionCanonicalAffineEmbedding`,
`IntersectionSectionsFlatBaseChange` and `SpectralFiniteCoequalizer` also compiled against
the sandbox overlay (26.2, 52.8 and 8.6 s); their identical temporary source copies were
removed from the packet. The original `import_prune_check.py` gate passes for the repaired
item. Both modified modules contain zero `sorry`s. The duplicate unit and composition
equations are explicitly resolved to `TopCat.Sheaf` in the repaired proof.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.sections_intersection_structure_colimit`
(node `lem-a1-sections-intersection-structure-colimit`). Added 0 holes. There are no remaining
`sorry` declarations in the delivered module and no new modules or split-off statements.
The proof uses the existing declarations of all six proof dependencies; no dependency
proof is copied into this module.

## No longer needed

Removed the six duplicate private declarations listed above in favor of the shared API.
No dependency node or module is pruned. All five original declared dependencies are
used. The approved `lem-weil-pbc-sets-inverse-image-composition` is also used directly.
Removed the original proof-only imports `Mathlib.Topology.Spectral.Basic`,
`Mathlib.CategoryTheory.Limits.Types.Filtered` and
`Mathlib.CategoryTheory.Sites.PreservesSheafification`: the actual proof dependency imports
supply the APIs used. Also removed an exploratory `Mathlib.Order.Shrink` import.
All original public imports remain.

The spectral index is already small in the required universe, so no shrinking construction is
needed. Only the open-embedding unit clause of the subspace coherence theorem is needed;
the ring-composition and homeomorphism clauses and the naturality clause of directed-ring
recognition are replaced here by proved adjunction/naturality arguments. Their modules remain
needed, and no declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned packet correctly identified duplicated lemmas. They had been copied because
the originals were private; the repair exposes and uses the existing declarations in place.
No false statement or definition was found. The old proof plan described naturality through
homeomorphism coherence and colimit functoriality; the exact Lean conclusion asks for a unique
sheaf map characterized on every open. Constructing that map by the inverse-image adjunction
proves precisely this stronger characterization directly. The updated node records the actual
argument. The empty-intersection and repeated-open cases require no additional hypotheses.

Change record: `coord/changes/D6-intersection-sections-proof-scopes.md` documents the
added command scopes required by preflight. The public statement is verbatim unchanged.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
