## What changed

Proved all five clauses of `AlgebraicGeometry.Scheme.etale_kflat_criteria` in
`Sheaf.Paper.EtaleKFlatCriteria`, preserving its signature and all public imports.
The bounded-flat clause uses the proved independent-universe criterion, which accepts
`IsFlatOnSite` directly. Total tensor induces a triangulated functor on the homotopy
category, so the triangulated subcategory of acyclic complexes gives all three
pairwise implications. The cone clause specializes that result. A proved private
helper `acyclic_colimit` supplies the exact-colimit argument; tensor preserves
colimits, and the last clause combines the bounded-flat and filtered-colimit clauses.
Updated the existing node's proof, proof dependencies and proof origin accordingly.
No statement, definition, target, or other module was changed. No new nodes or holes.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.etale_kflat_criteria` (node `lem-kun-kflat-criteria`).
Proved 1 of 1 original sorries; 0 sorries remain and 0 were added. This is a proof,
not a decomposition. The new private helper is completely proved.
The final pruned module compiled in 22.0 seconds; `#print axioms` for the theorem
reported exactly `propext`, `Classical.choice`, and `Quot.sound` (no `sorryAx`).
Resumed validation on 2026-10-19: the retained module compiled cleanly against
the current server snapshot in 11.8 seconds, and again in 13.7 seconds on this retry. Its theorem signature and all
public imports still match the current source; the four replacement library
imports introduce no cycle, and the node dependencies equal its proof-step uses.
The five original clauses retain arbitrary schemes and commutative coefficient rings,
arbitrary representative isomorphisms, arbitrary small filtered indexing categories,
and upper bounds which may vary with the diagram object. No nonzero-ring, lower-bound,
or common-bound assumption was added. The filtered category is nonempty by its own
`IsFiltered` instance; zero objects and zero rings require no separate argument.

## No longer needed

Removed these proof-only imports and corresponding dependency nodes from this route:

- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: its derived-category tensor
  construction is not used by a criterion about total tensors of actual complexes.
  The statement dependency `def-kun-derived-tensor` remains as the K-flat convention.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`, node
  `lem-pc-bounded-above-flat-kflat-site`: replaced with the already-proved
  `lem-weil-pbc-independent-bounded-flat-kflat`, accepting the actual flatness API
  and independent site universes without transporting the entire module category.
- `Sheaf.Algebra.Homology.KFlatTensorConeTwoOutOfThree`, node
  `lem-pc-kflat-tensor-cone-two-out-of-three`: the existing source triangulated
  bifunctor proves the general triangle clause directly, and the cone is a specialization.
- `Sheaf.Algebra.Homology.FilteredColimitsTensor`, node
  `lem-pc-module-filtered-colimits-tensor`: the proved independent-universe tensor
  preservation API plus Mathlib's exact sheaf colimits gives exactly what is used.

Withdrawn all three obsolete top-level `tool_uses` approvals. Two already-proved tools
from another unit are used: `lem-weil-pbc-independent-bounded-flat-kflat` and
`lem-weil-pbc-independent-sheaf-tensor-colimits`. They are the existing independent-
universe versions of the old tools; no declaration of this unit supplies the actual
`IsFlatOnSite` interface and separate site-morphism universe. The maintainer records
any necessary approvals; this delivery does not add or reorder approvals. The unit's
`realized.statement` and `realized.steps` are empty, so no fixed unit step is bypassed.
These modules are unnecessary for this item's proof; this does not assert they are
unreachable from every other target consumer.

## Where the brief, the DAG or earlier work was wrong

The original proof imports use the older same-universe `IsFlat` interface, whereas
this theorem assumes `IsFlatOnSite` on the small etale site. The existing independent-
universe bounded-flat theorem already resolves both differences. The planned explicit
cone comparison and signed homotopy calculation are already proved by the source
bifunctor API; using its triangulated instance removes that duplicated work.

The current blueprint's final bounded-below flat corollary was already corrected in
this node before this session. This delivery preserves that corrected statement and
does not claim the incorrect corollary. Stacks `sites-cohomology.tex`, labels
`lemma-bounded-flat-K-flat`, `lemma-K-flat-two-out-of-three` and
`lemma-colimit-K-flat`, were read against the final argument.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
