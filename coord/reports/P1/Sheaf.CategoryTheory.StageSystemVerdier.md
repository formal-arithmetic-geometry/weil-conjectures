## What changed

Proved `CategoryTheory.StageSystem.commonStage_verdier_existsUnique` in
`Sheaf.CategoryTheory.StageSystemVerdier` without changing its statement or public
imports. Added proved private helpers for the common-stage pretriangulated axioms
and uniqueness. The only new import is the private proof import
`WeilConjectures.CategoryTheory.Idempotents.Pretriangulated`, for transfer of the
triangle-morphism axiom along triangle isomorphisms.

The TR3 proof represents the first two components at a common stage, descends the
commuting equation, applies the stage axiom, and transports the resulting triangle
morphism using `mapTriangleIso (S.transIso h)`. Thus the supplied shift compatibility
suffices for the arbitrary shifts in the theorem. For TR4, `IsTriangulated.mk'`
allows choosing all three cones at the representative stage and mapping its
octahedron. Updated the assigned node's proof and provenance to match this route.
All helper lemmas are private and completely proved; there are no new public
statements, modules, definitions, or instances.

Validation: the complete proof compiled in 5.3 seconds on the server. The explicit
axiom check for `CategoryTheory.StageSystem.commonStage_verdier_existsUnique`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`. The delivery checks
compile the final file after replacing the diagnostic `simp?` calls by their
suggested `simp only` proofs and removing the axiom-printing command.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.StageSystem.commonStage_verdier_existsUnique`, node
`lem-route-common-stage-verdier-exists-unique`.

Original holes: 1. Closed: 1. Added: 0. Remaining in the item: 0.
No statements were split off and no `sorry` remains anywhere in the delivered Lean.

## No longer needed

None: no existing imports or declared dependencies were removed, and no existing
node or module was pruned. The initial node had empty `proof_deps`.
The canonical-shift `WeilConjectures.CategoryTheory.StageSystem.Pretriangulated`
and `.Triangulated` modules were read for their proofs but need not be imported:
their instances require additional coherence assumptions. Their declarations and
all source-library files remain unchanged.

The implementation of TR4 uses `IsTriangulated.mk'` and therefore does not require
the docstring's more elaborate descent of three previously selected cone triangles.
The unit's own statement and proof route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The assigned node was provisional and had no numbered proof steps or proof
dependencies despite the substantive proof described in the Lean docstring. Its
proof is now recorded. The existing source-library instances cannot be applied
directly with the theorem's arbitrary pair-category shifts; transporting complete
triangle morphisms through the assumed shift-compatible `transIso` supplies the
needed argument without adding hypotheses. No statement or definition repair was
necessary.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
