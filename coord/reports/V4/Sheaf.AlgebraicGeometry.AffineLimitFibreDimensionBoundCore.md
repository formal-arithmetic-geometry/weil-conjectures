## What changed

Replaced `AlgebraicGeometry.fibre_dimension_contradiction_of_all_stages_bad` by the bad-locus argument of Stacks Tag 05M5. The proof constructs the fixed-residue-field pushout diagram, proves its colimit universal property, and proves stabilization from finite generation of a Noetherian kernel and the elementwise filtered-colimit criteria. All helpers are private proved theorems in the item module. The original statement is unchanged. Updated its node to describe this proof.

The scheme-level `isOpen_localFibreDimension_le` and `fibre_dimension_after_base_change` provide the openness and dimension comparisons. Mathlib `exists_mem_of_isClosed_of_nonempty` packages the reduced closed subscheme limit construction.

## Proved and sorry left

The proof closes the one original hole, `AlgebraicGeometry.fibre_dimension_contradiction_of_all_stages_bad` (node `lem-weil-pbc-affine-limit-fibre-dimension-bound-core`). No holes or new statements with postponed proofs were added. The resumed delivery dry run compiled the complete module and passed the server preflight, including its declaration probes. Zero textual holes remain; zero holes were added or split off.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension`, `Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs`, and `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`. Their roles are packaged by the scheme-level comparisons and Mathlib closed-locus limit theorem. The corresponding nodes `lem-weil-pbc-dimension-at-point-field-extension`, `lem-weil-pbc-fibre-dimension-bounded-open-upstairs`, and `lem-weil-pbc-reduced-induced-closed-subscheme` are no longer direct proof dependencies; they remain available transitively where needed. No unit statement or realized proof step is bypassed.

Also removed redundant Mathlib proof imports already publicly provided by the remaining imports: `WeilConjectures.Mathlib.Topology.KrullDimension`, `Mathlib.RingTheory.RingHomProperties`, `Mathlib.RingTheory.RingHom.Surjective`, `Mathlib.RingTheory.RingHom.FiniteType`, `Mathlib.RingTheory.Noetherian.Basic`, `Mathlib.CategoryTheory.ConcreteCategory.EpiMono`, `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, `Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks`, `Mathlib.AlgebraicGeometry.Fiber`, `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.

## Where the brief, the DAG or earlier work was wrong

The preserved scratch helpers had not been compiled because of the earlier server outage. Fixed their pushout orientations, colimit-map rewriting, dependent fibre-point comparison and residue-field pullback pasting. The current proof uses the canonical scheme residue field to avoid constructing an arbitrary residue-field extension witness.

The compile server intermittently returns no answer (exit 124 without invoking Lean); these failures are distinct from file compilation timeouts. The resumed dry run succeeded against the current sources. No tool was modified or bypassed.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
