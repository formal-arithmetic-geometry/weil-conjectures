## What changed

Completed the existing sandbox proof of
`AlgebraicGeometry.exists_rightAdjointTensorComparison_projection` in
`Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonProjection`. Its original signature and
public imports are unchanged. Added proof-only imports for perfect tensor-Hom duality,
monoidal conjugation, perfect generation, coproduct preservation, and quasi-coherent closure.
The proof constructs the natural projection mate, proves its perfect-object, retract and
coproduct cases, uses shift/cone closure, applies perfect generation, and inverts the component
with the pinned inverse equation by reflexivity. Simplified its final existential construction.

The prior attempt already contained the main proof and the unfinished helper module but had
no node or report. Both modules compile together with the prescribed launcher. Added the
missing helper node and updated the original node's proof, proof_deps and proof_origin to
follow the actual proof. No definitions, existing signatures, visibility or targets changed.
The first worker edited only the two delivered Lean modules, their two node files, this report
and the search log. The second reader used temporary axiom-check copies and removed them.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.exists_rightAdjointTensorComparison_projection`
(node `lem-sc-right-adjoint-tensor-comparison-projection`). No direct sorry remains in the
item's module.

Added one direct hole:
`AlgebraicGeometry.projectionComparison_triangles`, in
`Sheaf.AlgebraicGeometry.ProjectionComparisonTriangles`
(node `lem-sc-projection-comparison-triangles`). Its proof is exactly `by sorry` and its
docstring states the source and full argument. This is the shift/cone step only; it does not
assert that the locus contains perfect complexes, is closed under coproducts or retracts,
or contains all objects. The main theorem supplies these other steps in Lean.

Counts: one original hole closed, one smaller hole added, net zero direct holes.
This is a decomposition, not a claim of a sorry-free projection formula. Existing imported
statements may still depend on sorry; they are intended downstream stage-3 items, not newly
added holes. In particular coproduct preservation by derived tensor is an existing statement.

The new helper was checked on shift zero, zero E, zero K, contractible triangles, and vertex
isomorphisms. Its argument uses exactness and compatibility of the mate, not invertibility of
the counit, perfection of E, tensor-unit quasi-coherence on Z, or any equation between the
scheme and localization universes. The coproduct step of the main proof covers empty families.

## No longer needed

No original import was removed: all five original public imports are needed by the unchanged
statement. Every added proof import is used: PerfectTensorHomDuality for the exact pairing;
MonoidalProjectionConjugate for identifying its mate; DerivedQCohPerfectGeneration for the
localizing closure argument; ProjectionComparisonTriangles for shifts/cones;
Mathlib.CategoryTheory.MorphismProperty.Retract for natural-transformation retracts;
DerivedTensorRightCoproducts and DerivedDirectImagePreservesDirectSums for preservation;
DerivedQCohDirectSumsAux for ambient sums and quasi-coherent closure; DerivedTensorQCohClosure
and DerivedPullbackTensorQCoh for the quasi-coherent diagram seen by direct image.

No node/module is claimed globally pruned. The original proof_deps were definitions used to
state the theorem, not a decomposition of its proof; they remain in stmt_deps. The updated
proof_deps replace that placeholder route with the actual named results. Explicitly, the old
proof dependency ids are `def-pc-derived-pullback`, `def-pc-derived-direct-image`,
`def-pc-scheme-derived-tensor-structure`, and `def-weil-proper-morphism`: all remain statement
dependencies and their defining modules remain imported; none is globally pruned. The global perfect
generation argument avoids any additional affine-locality or affine-equivalence imports.
`Sheaf.AlgebraicGeometry.ProjectionFormulaLocality` and the two locality directions were
searched and are not imported or needed by this proof. The existing
`RightAdjointTensorLocusTriangles` concerns the further right-adjunction mate and depends on
this projection theorem through its natural comparison, so using it here would be circular.

## Where the brief, the DAG or earlier work was wrong

The item's original citation Tag 0A9U is about the right adjoint tensor comparison for perfect
proper morphisms, not the projection formula asserted here. Read the actual sources at
https://stacks.math.columbia.edu/tag/08EU and https://stacks.math.columbia.edu/tag/0A9U.
Tag 08EU is the correct unbounded quasi-coherent projection formula. The theorem docstring
and proof_origin now cite it; the source field is not changed because stage 3 does not own
that field. Tags 08DT and 08DZ supply the coproduct background. The proof uses perfect duality
and the global perfect generation theorem rather than an affine reduction, preserving the
unit route (the unit's realized lists contain no bindings to bypass).

There is no applicable existing lemma stating shift/cone closure of this projection mate.
Mathlib has triangle two-out-of-three and shift lemmas, but their geometric comparison
compatibility is the remaining helper obligation. The existing lem-pc-projection-formula node
has an ordinary higher-direct-image statement for invertible modules recorded in Lean; that
signature cannot prove the unbounded assertion for arbitrary K and E here. Searches of the
whole blueprint for projection formula and projection mate found no duplicate of the helper.
LeanSearch returned Internal Server Error and is recorded as unavailable, not no-match.

The original node's blueprint ancestor command returns None because its created.item is a
module name; the new node follows the explicit ancestry of the parent natural-comparison node
to lem-sc-finite-duality and records the intermediate nodes. This is a metadata defect of the
existing projection node, not permission to alter the unit or target statements.

## New nodes

`lem-sc-projection-comparison-triangles`, file
`dag/nodes/sec-picard-framework/lem-sc-projection-comparison-triangles.json`, matches
`AlgebraicGeometry.projectionComparison_triangles` in the new module
`lean/Sheaf/AlgebraicGeometry/ProjectionComparisonTriangles.lean`. It states only the shift
and third-triangle-object closure of the projection-mate isomorphism locus, a strictly smaller
part of the projection-formula argument. Its source is Stacks Tag 08EU's exactness argument
with the canonical map of Cohomology equation the project server. Three actual search kinds are
recorded, with LeanSearch unavailable. No change records or forced adaptations are needed.

## Second reading by P1

1. **Interface: pass.** Read both delivered modules and compared the existing module with the
   repository using `diff`. Independently extracted the theorem signature through `:= by`: it
   is byte-for-byte unchanged. The five public imports, visibility, universes and definitions
   are unchanged. The existing node differs only in `proof`, `proof_deps`, `proof_origin`.
   There is no statement change or change record.
2. **Kernel check: pass as a decomposition.** Compiled both files together with `lcompile.py`
   in import order, without errors or warnings. Temporary copies with `#print axioms` give
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for both declarations.
   The only direct hole delivered is the named public theorem
   `AlgebraicGeometry.projectionComparison_triangles`, whose body is exactly `by sorry`;
   no definition, private helper, axiom or alternate implementation is added. The main proof
   uses existential duality data only inside its propositional proof; its final isomorphism
   uses the canonical mate and its proved `IsIso` instance, not an arbitrary existence witness.
3. **Split statement: pass.** Read its full signature, docstring and node. It asserts only
   preservation of the isomorphism locus under shifts and third vertices, so it cannot replace
   the perfect-object or coproduct arguments. Checked shift zero, the zero tensor factor,
   contractible triangles, and transport by vertex isomorphisms. The empty coproduct case is
   covered by the main proof's unrestricted `J`. Independently read Stacks Tag 08EU and
   confirmed that its exact-functor argument is the relevant source, while 0A9U concerns the
   further right adjoint. The helper explicitly transports shift comparisons for the supplied
   monoidal structure and does not silently assume that it is the canonical model's structure.
   Searched with different terms through LeanFinder, Loogle and grep, and searched both Lean
   roots. Found `Adjunction.commShift_rightAdjointProjectionMap_app` upstream, but it requires
   the tensorator/adjunction shift compatibility that is precisely not yet provided here; it
   does not close this hole in a few minutes. Mathlib's `isIso₃_of_isIso₁₂` supplies the final
   triangle step, not the geometric comparison. `RightAdjointTensorLocusTriangles` concerns
   the further adjunction and imports this item indirectly, so cannot be used here.
4. **Route and pruning: pass.** Followed the proof from its final canonical `asIso` back through
   perfect generation, coproduct preservation, retract naturality, and perfect duality. The
   helper supplies only the remaining shift/cone step. Added imports are proof-only and each
   supplies a referenced declaration or the retract API. The original statement imports
   remain necessary. Read `dag/units/sk-thm-picard-duality.json`: its `realized.statement` and
   single `realized.steps` list have no bindings for this item to bypass. No module is claimed
   globally pruned; the four original placeholder dependency ids are now explicitly accounted
   for under No longer needed.
5. **DAG: pass.** Checked that each node's proof dependency set is the union of its step uses
   and that every main-proof dependency names the declaration actually used. The new node's
   verbatim Lean statement agrees with its module, and its source, proof, searches, creation,
   ancestry, unit, chapter and Lean record are present. Both proof origins describe the route
   used, including the global perfect-generation replacement for affine reduction.

Second reading changed only this report: added the review, explicitly listed the four old
placeholder proof dependencies, and recorded temporary axiom checks accurately. No Lean proof,
statement, definition or node needed repair. One original hole is closed and one strictly
smaller hole is added; this remains a decomposition with net zero direct holes.
