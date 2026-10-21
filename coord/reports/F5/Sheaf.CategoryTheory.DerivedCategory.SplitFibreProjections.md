## What changed

Proved `DerivedCategory.split_fibre_projections` in
`Sheaf.CategoryTheory.DerivedCategory.SplitFibreProjections` with its complete original
statement and all three public imports unchanged. Added three proved private helpers:
`projection_isIso`, `graph_image_kernel_fst`, and `graph_image_kernel_snd`.
No definitions, instances, public signatures, or other Lean modules changed.

The prescribed second arrow has an explicit section after conjugating by β and γ.
Mathlib makes the first arrow monic. Lift the graph by `Triangle.coyoneda_exact₂` and
cancel that monomorphism to obtain a two-sided inverse to the specified projection.
The triangle identity gives the equality between its two components. Mapping these
identities through each homology functor gives monicity and the graph-image equality;
two explicit subobject factorizations identify each graph image with the claimed kernel.
The accompanying DAG proof and dependencies now describe this direct argument.

Validated the whole module through `lcompile.py`: clean compile, 5.1 seconds, no warnings.
The argument uses only Mathlib and does not depend on any holed project theorem.
Zero summands, zero h/r, characteristic two, and arbitrary integer degrees require no
extra assumptions; the proof uses only additive category identities and works unchanged
in these cases. The enclosing unit route is unchanged: the parent still receives every
split-projection and graph-kernel clause with its prescribed vertex identifications.

## Proved and sorry left

Closed the sole original hole, `DerivedCategory.split_fibre_projections`
(node `lem-sp-derived-split-fibre-projections`). Proved 1 of 1 original sorries.
Added zero holes; zero sorries remain in the delivered Lean module. All three private
helpers are fully proved. This is a proof, not a decomposition.

## No longer needed

Removed these proof dependencies from this node:

- `lem-sf-derived-homology-long-exact`: no connecting-map argument is needed; the
  projection inverse is constructed in the derived category, and monicity on homology
  follows from its factorization through an isomorphism.
- `lem-weil-pbc-unbounded-derived-iso-cohomology`: the two inverse identities are
  proved directly, so cohomological detection of isomorphisms is unnecessary.

These are Mathlib leaves; no project Lean module is withdrawn or deleted, and no global
unreachability is claimed. No import was added or removed. All three retained public
imports supply objects in the unchanged statement (`homologyFunctor`, subobjects, and
`Functor.biprodComparison`). The retained HomologySequence import supplies the homology
functor itself even though its long exact sequence is unused.

## Where the brief, the DAG or earlier work was wrong

The original eight-step proof plan was valid but longer than necessary. The triangle
Hom-exactness already supplies the lift needed for a direct inverse, while Mathlib
provides the monicity of the first triangle arrow when the second one is epic.
The replacement stays below the unit level and preserves the statement verbatim.
No statement or definition repair was needed. No interrupted delivery or prior proof
edits were present in the sandbox at resumption.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
