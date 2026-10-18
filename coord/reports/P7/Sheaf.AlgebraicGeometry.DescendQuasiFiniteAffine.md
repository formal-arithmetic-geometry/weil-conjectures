## What changed

Proved `AlgebraicGeometry.descend_isQuasiFinite_affine` with its existing signature.
Constructed the directed-tail pushout diagram, its colimit cocone and universal property,
and the isomorphisms showing transition comparisons are surjective. Applied the existing
`AlgebraicGeometry.exists_stage_fibre_dimension_le` with dimension bound zero.
Three proved private helpers convert the project's quasi-finite predicate to Mathlib local
quasi-finiteness, obtain the limit fibre dimension bound, and recover quasi-finiteness from
the descended bound. The final conversion uses Mathlib's locally Artinian fibre topology.
Updated the item node and theorem proof description to match this route.

The source checked was `literature/stacks-project/limits.tex`, labels
`lemma-limit-dimension` (05M5) and `lemma-descend-quasi-finite` (094M).
The item realizes no statement or step of its blueprint unit; the unit route is preserved.
The original public imports, theorem signature, and all definitions are unchanged.
The cleaned proof compiled remotely in 8.0 seconds; the delivery axiom probe ran.
A docstring-spacing warning was corrected before the final dry run.

## Proved and sorry left

Closed one of one item holes: `AlgebraicGeometry.descend_isQuasiFinite_affine`
(node `lem-weil-pbc-descend-quasifinite-affine`). No holes added or split off.
No `sorry` remains in the delivered Lean file.
The proof uses the already stated `AlgebraicGeometry.exists_stage_fibre_dimension_le`
(node `lem-weil-pbc-affine-limit-fibre-dimension-bound`), whose existing proof is still
`sorry`; this delivery does not claim to close that dependency.

## No longer needed

Removed proof imports:
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Limits`
- `Mathlib.Topology.KrullDimension`
- `WeilConjectures.Mathlib.Topology.KrullDimension`
- `Sheaf.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite`
- `Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension`

The first four are supplied by the retained imports where their APIs are used.
The source-library topology extension is unnecessary. The last two modules, with nodes
`pqf-lem-qf-locqf-qc` and `lem-weil-pbc-ring-quasifinite-zero-fibre-dimension`, are
unnecessary for this proof: the quasi-finite predicate is assembled directly from local
finite type, affine quasi-compactness and open fibre singletons. The pointwise local
dimension node `def-kun-topological-dimension-at-point` is also unnecessary; the global
zero-dimensional bound suffices by the locally Artinian criterion.
This reports pruning of this proof's dependencies, not an assertion that these modules
are unreachable through all other targets. Removed the obsolete top-level tool approval
for `pqf-lem-qf-locqf-qc`; all other approvals retain their order.

## Where the brief, the DAG or earlier work was wrong

No false statements or unusable dependency interfaces were found. The planned detour
through dimension at a point and the project's ring-level quasi-finite criterion was
longer than the available Mathlib Artinian fibre argument. Chosen categorical colimits
need explicit comparison with the supplied cocone; the proof constructs these comparison
isomorphisms and verifies commutation rather than identifying them definitionally.
Zero rings and empty fibres are handled uniformly: no nontriviality or fibre-point
existence is introduced. No target or intermediate signature was changed.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
