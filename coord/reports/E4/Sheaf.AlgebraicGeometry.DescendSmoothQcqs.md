## What changed

Completed AlgebraicGeometry.exists_eventually_smooth_of_isLimit_qcqs in
Sheaf.AlgebraicGeometry.DescendSmoothQcqs, with its signature unchanged. Two private proved
helpers implement finite affine-chart descent under qcqs hypotheses and transport between
the bundled Over.pullback maps and ordinary pullbacks. Open-immersion cancellation is
proved inline using the Mathlib pullback-pasting API. The helpers reuse the finite-chart and identity-stage comparison patterns already proved
in AffineSourceLimitSmoothStage and the source AffineTransitionLimit file, while removing
the irrelevant Noetherian hypotheses. The affine algebra step reuses the existing proved
Scheme.exists_smooth_stage_of_affine_diagram, which applies
CommRingCat.exists_smooth_pushout_stage. No other Lean module is modified.

The item node now records the actual base-change-to-Y₀ route and the proved affine-diagram
bridge. It retains the source's affine-local argument, finite common refinement, source
locality, and persistence by base change. The unit's realized statement and steps are untouched.

The full file compiled in 4.7 seconds before import cleanup; the final delivery checks compile
it again with the project probe. All Lean lines are at most 100 characters. Searches through
msearch LeanFinder, Loogle, grep, and repository rg found the reusable affine-diagram theorem
and the stronger Noetherian finite-chart proof. The latter was not applicable directly.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.exists_eventually_smooth_of_isLimit_qcqs
(lem-weil-pbc-descend-smooth-qcqs).

Original holes: 1. Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
All private helper theorems are proved. No split-offs, new modules, definitions, or axioms.
Finite covers and common refinements also handle the empty-source and empty-chart cases.
No nonempty scheme, Noetherian stage, or faithful-flatness assumption is introduced.

## No longer needed

Removed imports:
- Sheaf.AlgebraicGeometry.LimitAffineTransition (public): no limit construction is used;
  the given limiting cone suffices. Its declarations are not used by the proof.
- Sheaf.RingTheory.SmoothPushoutFilteredColimitStage (direct proof import): reached through
  the proved AffineDiagramSmoothStage bridge, so its theorem remains an actual dependency.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: only smooth base-change stability is used,
  already provided by Smooth; no properness assertion is needed.
- Mathlib.AlgebraicGeometry.Limits, Mathlib.AlgebraicGeometry.OpenImmersion,
  Mathlib.RingTheory.Smooth.Basic, Mathlib.Topology.Defs.Filter: redundant direct imports;
  the remaining imports provide the used cover, pullback, smoothness and compactness API.

The original explicit ring/spectrum comparison dependencies are now encapsulated in the
proved lem-sbc-affine-diagram-smooth-stage: lem-weil-pbc-affine-opens-induced-ring-map-spec-square,
lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-smooth-ring-map-base-change-composition,
and lem-weil-pbc-smooth-ring-map-iff-smooth-affine are not separately used by this proof.
The arbitrary-open factorization lemma lem-weil-pbc-morphism-factors-through-open-subscheme
is not needed: the finite cover construction and pullback comparisons give the maps directly.
The explicit existence theorem lem-weil-pbc-limit-affine-transition is not used in the proof;
only elementary base-change preservation of the given limit is needed. The approved ring
pushout descent node remains used transitively by the affine-diagram bridge, and
lem-pc-proper-base-change is used only for its smoothness base-change clause.
No claim is made that these shared modules disappear from every target's import closure.

Public-import pruning and its complete consumer list are recorded in
coord/changes/descend-smooth-qcqs-import-pruning.md. No consumer needs adaptation.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The existing Noetherian affine-source theorem
has stronger assumptions than this item, but its finite-chart construction works here because
compactness of the source and quasi-separatedness of the target already imply that the map
is quasi-compact. The implementation works over the system base changed to Y₀; hence it need
not construct affine triples relative to S₀ explicitly. This is the same affine-local proof
of Stacks Tag 0C0C. No signatures or mathematical definitions were repaired.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
