## What changed

Proved all nine holed theorems in
`Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting`, preserving every
existing statement and the canonical comparison definition. Added two proved private
helpers: the component formula and the paired truncation composition laws. Naturality
is the two truncation naturality equations followed by shift compatibility; composition
uses naturality of the lower comparison and of the shift comparison. The square laws
expand naturality for composite functors. Horizontal pasting applies the square law to
an explicitly associated and whiskered pasted isomorphism, then expands composition;
vertical pasting applies naturality to the composite natural transformation.

Updated the existing node's proof, proof dependencies and proof origin to match this
argument, and removed its obsolete heart-theorem tool approval. No signatures,
definitions, public imports or source-library modules changed. The scoped proof
commands are documented in
`coord/changes/cohomology-comparison-pasting-proof-commands.md`, as requested by preflight;
consumer search finds zero downstream Lean modules.

## Proved and sorry left

Closed nine holes, all attached to `lem-a1-cohomology-comparison-pasting`:

- `CategoryTheory.Triangulated.TStructure.cohomologyComparison_idTExact`
- `CategoryTheory.Triangulated.TStructure.cohomologyComparison_compTExact`
- `CategoryTheory.Triangulated.TStructure.cohomology_comparison_pasting`
- `CategoryTheory.Triangulated.TStructure.truncationCohomologyComparison_naturality`
- `CategoryTheory.Triangulated.TStructure.truncationCohomologyComparison_comp`
- `CategoryTheory.Triangulated.TStructure.truncationCohomologyComparison_id`
- `CategoryTheory.Triangulated.TStructure.truncationCohomologyComparison_square`
- `CategoryTheory.Triangulated.TStructure.truncationCohomologyComparison_paste`
- `CategoryTheory.Triangulated.TStructure.truncationCohomologyComparison_vertical`

No holes left in the item; no holes added or split off. The two private helpers are proved.
Single-file validation through `lcompile.py` passed cleanly in 11.5 seconds, with no
compiler errors or warnings. Local proof-scoped transparency settings handle the
existing truncation definitions; no definition was changed.

## No longer needed

Removed the private import
`WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`.
The proof does not use `lem-weil-heart-short-exact-triangles`: Mathlib already supplies
the bounds on `truncGELE j j`, and `isLE_shift`, `isGE_shift` and `mem_heart_iff` prove
heart membership directly. Removed that node from `proof_deps`, the first step's `uses`,
and the top-level `tool_uses`. This does not assert that the homology module or that node
is unused by other targets. The canonical truncation-comparison node remains needed.
No module is withdrawn and no unit statement or route changes.

## Where the brief, the DAG or earlier work was wrong

The planned heart-construction dependency is unnecessary for this proof: its elementary
bound assertions are already in Mathlib. Horizontal pasting can be obtained directly by
applying the square theorem to the explicitly pasted shift-compatible isomorphism;
this is the same comparison law with all associators retained.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
