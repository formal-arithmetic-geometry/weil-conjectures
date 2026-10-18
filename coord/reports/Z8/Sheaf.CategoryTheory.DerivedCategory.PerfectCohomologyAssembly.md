## What changed

Proved `DerivedCategory.isPerfectRingComplex_of_perfect_cohomology` in
`Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly`, with its signature unchanged.
The proof follows all five steps of `lem-sf-perfect-cohomology-assembly` and Stacks
More on Algebra, Tag 066U, `lemma-cohomology-perfect` (read in the local source).
Three proved private helpers transport perfectness across isomorphisms, shift a bounded
finite-projective model, and construct the zero-object model.

The main proof fixes a complex representative and its cohomology identifications, transfers
the cohomology bounds, shifts the degree-zero perfect cohomology models, and inducts on
`n : ℕ` to prove perfectness of `Q(C.truncLE (a + n - 1))`. The base is zero by
standard t-structure orthogonality. Each successor applies
`DerivedCategory.isPerfectRingComplex_obj₂_of_distTriang` to the triangle supplied by
`DerivedCategory.truncation_triangle`. The final truncation inclusion is a quasi-isomorphism.
The separate case `b + 1 < a` uses orthogonality to show the entire object is zero, so no
ordering hypothesis has been added. The adjacent-bounds case `a = b + 1` is also covered.

Added a proof-only import of
`Sheaf.CategoryTheory.DerivedCategory.PerfectRingTriangleClosure`.
Imported the upstream truncation module directly, matching the dependency node's current
Lean attachment. No definitions, public signatures, DAG route, or unit realizations changed.
The unit `sk-prop-sf-biduality-general` has no numbered steps realized by this node.

Searches through launcher msearch: LeanFinder for bounded perfect cohomology returned
standard t-structure and representative lemmas; Loogle `DerivedCategory, "Perfect"`
returned no results; grep `IsPerfect|perfect.*cohomology` returned unrelated names.
Repository searches found the stated arbitrary-localization-universe triangle-closure lemma;
upstream `IsPerfect` helpers have a more restrictive localization universe, so the private
helpers prove the identical elementary constructions directly for `IsPerfectRingComplex`.

Validation: single-file launcher compilation succeeds without warnings. Both proof imports
pass `tools/import_direction.py may`.
The dry run requested a change record for the two added file-local open commands:
`coord/changes/z8-perfect-cohomology-proof-scopes.md`. Its consumer table records the
single downstream module, whose signatures are unaffected. This record sends the delivery
for independent CODEX review.

## Proved and sorry left

Closed one original hole:
`DerivedCategory.isPerfectRingComplex_of_perfect_cohomology`
(node `lem-sf-perfect-cohomology-assembly`).

There are zero remaining holes in the item, zero added holes, and zero split-offs.
All three private helpers are proved. The proof uses the already stated theorem
`DerivedCategory.isPerfectRingComplex_obj₂_of_distTriang`
(node `lem-sf-perfect-ring-triangle-closure`), whose existing sorry remains in its own,
unmodified module. This is a proof from the declared dependencies, not a claim that
all transitive dependencies are now sorry-free.

## No longer needed

Removed direct proof imports of `Mathlib.Algebra.Homology.Embedding.CochainComplex`,
`Mathlib.Algebra.Homology.Single`, and `Mathlib.CategoryTheory.Triangulated.Triangulated`;
the upstream truncation module publicly supplies this infrastructure.
Replaced the retired re-export `Sheaf.CategoryTheory.TruncationTriangle` with its actual
implementation module `WeilConjectures.CategoryTheory.TruncationTriangle`.

No declared dependency node is pruned: the proof uses
`def-weil-abstract-derived-category`, `def-pc-perfect-ring-complex`,
`lem-sf-perfect-ring-triangle-closure`, and `lem-weil-pbc-truncation-triangle`.
No module is withdrawn and no new node is needed.

## Where the brief, the DAG or earlier work was wrong

The item lacked the proof-only import of its declared triangle-closure dependency.
Its truncation import was a retired compatibility re-export; the node already names
the correct upstream module. Both import issues are repaired here. No mathematical
statement or proof-plan correction was needed.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
