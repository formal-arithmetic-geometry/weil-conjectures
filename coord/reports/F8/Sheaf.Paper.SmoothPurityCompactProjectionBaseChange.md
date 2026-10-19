## What changed

The original theorem `compact_projection_base_change` now has a complete Lean proof of
its proper and open mate calculations, compactification pasting, simultaneous naturality,
and inverse equation. It is assembled from the separate finite construction, tower
construction, and inverse-image tensor-square results listed below. Its signature is
unchanged. All original definitions were moved verbatim into
`Sheaf.Paper.SmoothPurityCompactProjectionData`, publicly reexported by the original module,
to avoid import cycles with the construction lemmas.

The tower ring sheaf is constructed explicitly by uncurrying `spCoefficientCommRings`.
The proof identifies the two vertical topologies and rebundles the identical module
presheaves as sheaves of modules. Its equivalence fixes whole presheaves and morphisms,
including the coefficient transitions. `tower_presentation_exists` uses this construction
and `normalized_tower_operations_exists`; it does not choose a ring system from a mere
existence theorem. No existing consumer needed adaptation: downstream.py returned zero.

All six modules compiled together after connecting the tower construction. The subsequent
import-pruned data module also compiled. The final delivery dry run verifies compilation,
axioms, node records and consumer checks again.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.CompactProjectionBaseChange.compact_projection_base_change`
is replaced by a complete proof from the three independent statements below. This is a
decomposition of one original hole into three holes, not a net proof closure: zero of the
one original hole is closed without new assumptions, one upper proof is assembled, three
holes are added, and zero textual holes remain in the item module.

The three remaining holes, and no others in the delivery, are:

- `finite_presentation_exists`, node `lem-sp-compact-projection-finite-presentation`,
  module `Sheaf.Paper.SmoothPurityCompactProjectionFinitePresentation`.
- `normalized_tower_operations_exists`, node `lem-sp-compact-projection-tower-operations`,
  module `Sheaf.Paper.SmoothPurityCompactProjectionTowerOperations`.
- `Presentation.tensor_square`, node `lem-sp-compact-projection-tensor-square`,
  module `Sheaf.Paper.SmoothPurityCompactProjectionTensorSquare`.

`tower_presentation_exists` is proved from the actual constructed system and the separate
operations theorem. The final item proves `tensor_mate_coherence`, `proper_compatibility`,
`properProjection_naturality`, `inverse_square`, `inverse_tensor_square`,
`open_inverse_compatibility`, `open_compatibility`, `open_target_compatibility`,
`forward_compatibility`, `diagramAssertion_of_forward`, and the final theorem assembly.
These are real categorical proofs; none is an alias of a new holed theorem.

The finite and tower construction lemmas contain no geometric compatibility conclusion.
The tensor-square lemma contains neither direct-image mates nor compact-support operations.
They are distinct source arguments, respectively the constant ring construction, the
varying coefficient operation construction, and the pure-tensor/totalization calculation.
Their docstrings and nodes give their complete intended proofs. They retain arbitrary
base change, the zero finite ring, empty schemes, unbounded complexes and nonflat
coefficient transitions. In the tower case exactness is asserted only for spatial inverse
image, not scalar extension along quotient-ring reductions. The proof never detects a
derived system equality by separate evaluations.

## No longer needed

Removed direct proof imports:
`Sheaf.Paper.RingedExchangeTensorCoherence`,
`Sheaf.Paper.ProjectionMateExact`, and
`Sheaf.CategoryTheory.DiagramSiteRealization`.
Their old proof dependencies `lem-weil-pbc-ringed-exchange-tensor-coherence`,
`lem-weil-pbc-ringed-projection-mate-exact`, and
`lem-weil-pbc-diagram-site-realization` are pruned from this item's route and approved
tool-use list. The proper mate argument is proved directly in independent category
universes; the open mate argument uses the already proved `Adjunction.projectionMap_mate`;
projection naturality is that of the actual projection natural transformation. The tower
realization uses `verticalDiagramSite_isSheaf_iff` directly and retains the varying ring.
These removals do not claim those modules are globally unreachable: other imports may
still require them.

Removed unused direct Mathlib imports:
`Mathlib.Algebra.Category.Grp.FilteredColimits`,
`Mathlib.CategoryTheory.Abelian.FunctorCategory`, and
`Mathlib.CategoryTheory.Sites.Limits`.

The relocated data no longer directly imports
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`,
`WeilConjectures.Compactification.BaseChange`,
`WeilConjectures.Compactification.Refinement`, or
`WeilConjectures.Compactification.RefinementCategory`.
The needed tensor interfaces already come through `OpenTensorNormalization`; the theorem
uses a compactification, with its definition imported directly, and no refinement argument.
The ringed tensor and open normalization declarations remain needed for the construction
lemmas and public interfaces; their DAG nodes are not pruned. No unit statement or step is
bypassed, and no existing Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The proposed generic ringed tensor-square API identifies its site-object and morphism
universes. Here the pro-etale sites have objects in Type (u+1) and morphisms in Type u.
It therefore does not specialize directly to this presentation. The new tensor-square
lemma retains the original universes and the same source calculation; it is the remaining
representative/transport argument, followed by K-flat descent.

The construction in the DAG's first step is substantive: the existing normalized-open
existence theorem supplies data for one open square, not the simultaneous presentation
with a single tensor model at every scheme, and its arbitrary-coefficient Pullback does
not supply exactness for every ring map. The new construction statements isolate exactly
these spatial, normalized coefficient cases. No statement has been weakened.

The initial remote-compiler timeouts are resolved; clean compiles were subsequently
obtained. The inherited continuation notes were stale and did not describe the compiled
state. Provider interruptions also reset the split-off reference clock: observed start
values were 1792426208.4345 and 1792437748.3557837 for the same F8 item; the user resumes did
not start a new mathematical task. The current brief markers identify the same item and
no distinct attempt identifier. No budget or launcher file was edited.

## New nodes

`def-sp-compact-projection-presentation`: the existing normalized coefficient,
operation, comparison and compact-support data, moved unchanged into the data module.

`lem-sp-compact-projection-finite-presentation`: simultaneous operations and invertible
open mates for the constant finite ring. This remains a construction hole.

`lem-sp-compact-projection-tower-operations`: simultaneous operations on an already
normalized varying ring system. This remains a construction hole.

`lem-sp-compact-projection-tower-presentation`: the actual constructed varying ring sheaf
and module-presheaf-preserving equivalence, combined with the operations theorem.
Its proof is complete relative to that operations theorem.

`lem-sp-compact-projection-tensor-square`: inverse-image tensor coherence before any
mate or compact-support construction. This remains the representative calculation hole.

Change record: `coord/changes/smooth-purity-compact-projection-data.md`.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
