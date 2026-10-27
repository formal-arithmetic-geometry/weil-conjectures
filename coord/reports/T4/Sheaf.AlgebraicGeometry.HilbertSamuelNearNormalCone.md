## What changed

Proved `AlgebraicGeometry.HilbertSamuel.near_normal_cone` by specializing the
already stated `near_normal_cone_nonreduced` to the identical input data. The
latter omits only the reducedness hypothesis and gives exactly the same conclusion,
including the specified Rees monomials, pullback and original scheme point.
No theorem signature or construction body changes.

Moved the five shared constructions (`centerStalkIdeal`, `centerResidueAlgebra`,
`normalFibre`, `normalFibreGrade`, `normalPolynomialGrade`) verbatim into the new
`Sheaf.AlgebraicGeometry.NormalConeFibreConstructions` module. Both existing
near-point modules publicly import it. This is the only change to the unclaimed
`SchemeNearPointNormalCone` module and breaks its former definition-only import
of the reduced theorem's module. The original fifteen public imports are preserved
in the new common module, hence publicly reexported by both original modules.

Updated the reduced theorem node's proof dependencies and removed its obsolete
five tool-use entries. Moved the existing definition node's Lean attachment to the
shared module; no new DAG nodes are introduced. The unit's realized statement and
steps do not name this node; its ancestor route is unchanged.

Validation: `lcompile.py --all` compiled the whole three-module delivery without
errors or warnings: common constructions 3.7 s, nonreduced module 21.6 s, reduced
module 21.8 s. This includes the sole direct importer of the changed reduced
module. Source checks confirm the moved block and theorem signature are verbatim;
the overlay import graph is acyclic and the stronger DAG node has no dependency
path back to the reduced theorem.

Change record: `coord/changes/T4-normal-cone-shared-constructions.md`.

## Proved and sorry left

Closed one of the item's one holes:
`AlgebraicGeometry.HilbertSamuel.near_normal_cone`
(`lem-trf-hilbert-samuel-near-normal-cone`). The item now has zero holes.
No holes added, and zero split-off statements.

The adapted existing module retains exactly its two pre-existing holes unchanged:

- `AlgebraicGeometry.HilbertSamuel.near_function_iff_raw`
  (`lem-per-scheme-near-point-normal-cone`).
- `AlgebraicGeometry.HilbertSamuel.near_normal_cone_nonreduced`
  (`lem-per-scheme-near-point-normal-cone`).

The new construction module has zero holes. This closes the reduced specialization
relative to the stronger existing theorem; it does not claim that the stronger
near-point theorem or the project's target closure is now free of sorry.

## No longer needed

No module is withdrawn or claimed globally pruned. The reduced theorem no longer
needs the original ten-step route separately: that work is already stated in the
stronger nonreduced theorem. The former proof dependencies removed from this node
are:

- `lem-weil-pbc-finite-type-over-noetherian`.
- `lem-pur-conormal-graded-algebra`.
- `lem-weil-pbc-smooth-scheme-over-field-regular`.
- `lem-sc-regular-local-domain`.
- `lem-weil-pbc-noetherian-finitely-many-components`.
- `lem-weil-pbc-spec-irreducible-components-minimal-primes`.
- `lem-weil-pbc-dimension-at-point-local-ring-trdeg`.
- `lem-weil-pbc-dimension-at-point-components`.
- `lem-sc-closed-irreducible-dimension-trdeg`.
- `lem-trf-bennett-normal-flat-numerical-criterion`.
- `lem-kun-transcendence-degree-tower`.
- `def-nagata-global-blowup-glue-data`.
- `def-nagata-global-blowup-local-model`.
- `def-nagata-affine-blowup`.
- `def-nagata-rees-algebra`.
- `lemma-nagata-relative-proj-base-change-arbitrary`.
- `lem-weil-pbc-minimal-prime-reduced-localization-field`.
- `lem-trf-flat-module-torsionfree-domain`.
- `lem-weil-pbc-nakayama-local-generators`.
- `def-pc-proj`.
- `def-pc-standard-graded-algebra`.
- `lem-trf-near-point-additive-symmetry`.
- `prop-nagata-relative-proj-functoriality`.

These may remain needed elsewhere, including by the nonreduced theorem; their
source declarations and DAG nodes are preserved. The five old generic tool-use
approvals on this node are removed because the specialization uses none of them.

The reduced module's old private proof imports are removed (the shared theorem now
supplies its proof):

- `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra`.
- `WeilConjectures.AlgebraicGeometry.Regular`.
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`.
- `WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg`.
- `WeilConjectures.RingTheory.DimensionAtPointComponents`.
- `Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`.

The original public imports are moved, not eliminated from the public dependency
surface. The sole new proof import is `Sheaf.AlgebraicGeometry.SchemeNearPointNormalCone`.
The nonreduced module's former public import of `HilbertSamuelNearNormalCone` is
replaced by the shared constructions module; this is necessary to keep imports acyclic.

## Where the brief, the DAG or earlier work was wrong

The original DAG plans the whole local argument again despite an already stated
stronger theorem with the exact same construction and conclusion. A source search
found it in `SchemeNearPointNormalCone`. Its public import of the reduced theorem
module was needed only for five definitions, so naive direct reuse would create a
cycle. Extracting those definitions resolves this architectural dependency without
weakening or restating a theorem. The stronger theorem is existing, not a new
split-off copy of this item. There are no disputed mathematical statements.

LeanFinder, Loogle and grep searches were run through `msearch.py`; no matching
Mathlib theorem was returned. The exact existing project theorem is preferable to
repeating its Bennett/directrix argument. Edge cases and nonclosed points are
inherited unchanged because the conclusion and all non-reducedness hypotheses
are syntactically identical; no witness, field action or fibre identification is changed.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
