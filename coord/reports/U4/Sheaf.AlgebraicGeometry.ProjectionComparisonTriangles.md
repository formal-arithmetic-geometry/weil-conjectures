## What changed

Replaced the whole proof of `AlgebraicGeometry.projectionComparison_triangles` in
`Sheaf.AlgebraicGeometry.ProjectionComparisonTriangles` with a compiling proof. Its existing
signature and docstring are unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.ProjectionComparisonExact`.

The new module constructs `AlgebraicGeometry.projectionComparisonNatTrans` with exactly the
mate in the original statement as each component. Its naturality is proved from adjunction
naturality, inverse tensorator naturality, and the whisker exchange identity. The construction
uses no unproved existence theorem and contains no hole.

The original module proves transport of invertibility along ambient isomorphisms by an
explicit naturality calculation. It proves shift closure by `NatTrans.app_shift`, constructs
the morphism of image triangles (including its connecting-map square), and applies
`Pretriangulated.isIso₃_of_isIso₁₂` before transporting to the third supplied object.

The geometric exactness and compatible shift structures are isolated in the new theorem
`AlgebraicGeometry.projectionComparison_exact`. This theorem supplies structure on the two
specified functors and the already constructed transformation; it does not assume or assert
invertibility of any component. The supplied monoidal pullback structure and adjunction are
unchanged. Updated the original DAG node's proof route and proof dependencies.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.projectionComparison_triangles`
(node `lem-sc-projection-comparison-triangles`). No sorry remains in the assigned module.

Added one whole-proof hole: `AlgebraicGeometry.projectionComparison_exact`
(node `lem-sc-projection-comparison-exact`), in the new module
`Sheaf.AlgebraicGeometry.ProjectionComparisonExact`. Its docstring gives its source and
representative-level proof plan. It is the only sorry added anywhere.

This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
The formal naturality, isomorphism transport, shift-conjugation and triangle two-out-of-three
arguments are complete. Exactness and shift compatibility on the geometric functors remain
open; no claim of a sorry-free proof of the original theorem's entire import closure is made.

Both modules compile individually in dependency order using lcompile.py. The existing
theorem's signature is unchanged, and the new definition uses no arbitrary witness selected
from an unproved existence assertion. Existential shift structures from the residual theorem
are eliminated only inside the proof of a proposition.

## No longer needed

No imports or modules pruned. All five original public imports are retained because the
statement uses their definitions or instances. The new proof-only import is used.

The displaced direct proof dependencies are `def-pc-scheme`, `def-pc-derived-category`,
`def-pc-derived-pullback`, `def-pc-derived-direct-image`,
`def-pc-scheme-derived-tensor-structure`, and `def-weil-proper-morphism`.
All six remain needed for statements and for the geometric residual lemma. They cease to be direct proof dependencies of the assigned node because the actual
proof uses `lem-sc-projection-comparison-exact`. None becomes globally unnecessary.
The unit `sk-thm-picard-duality` has no realized statement or proof-step node at this location;
its route has not been bypassed. No perfect-object, retract, coproduct, or locality lemma is
imported by this proof, and no such step was part of this node's planned closure argument.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies are definitions; their Lean signatures do not supply the
geometric shift and triangle compatibility asserted in the informal proof. The new residual
theorem records that missing diagrammatic exactness explicitly instead of treating it as a
typeclass instance. Mathlib supplies the formal shift-conjugation and two-out-of-three steps,
and upstream has generic projection-map shift compatibility and K-flat tensor shift results,
but these require compatible structures not yet supplied for the given geometric functors
and arbitrary supplied tensorator. No existing statement or definition was changed.

Tags 08DT and 08DZ concern coproducts. The relevant sentence for this item is the exactness
sentence in the proof of Tag 08EU; this delivery does not introduce coproduct dependencies.
LeanSearch was unavailable (Internal Server Error), which is recorded as unavailable.

## New nodes

`lem-sc-projection-comparison-exact`, in
`dag/nodes/sec-picard-framework/lem-sc-projection-comparison-exact.json`, states exactness
and shift compatibility for the concrete ambient natural projection transformation, without
an invertibility assertion. Its Lean module is
`Sheaf.AlgebraicGeometry.ProjectionComparisonExact`. This isolates the geometric part of
step 1 of the original proof; the shift-isomorphism and triangle-isomorphism conclusions are
proved in the assigned module. The node includes all three search kinds, with LeanSearch's
service failure recorded, and a complete natural-language proof plan.

Edge cases checked against the new statement: for E = 0 both functors are zero and the
component is the zero-object comparison; for f = identity the comparison is made from the
inverse tensorator and the adjunction counit, rather than an assumed identity; shift zero is
included in CommShift coherence; contractible triangles are handled by exactness and the
same Mathlib theorem. No assumption that arbitrary components are invertible is used.
Blueprint search found no existing blueprint statement for this exact realization.
No change records or forced adaptations are needed: existing signatures, definitions,
visibility and public imports are unchanged.

## Second reading by U4

1. **Interface preservation — pass.** Read both delivered modules and diffed the assigned
   module against the repository version. The sole existing declaration retains its entire
   signature and docstring byte for byte. Only its proof and one plain, proof-only import
   changed. No existing definition, public import, target statement, or visibility changed;
   no change record or forced adaptation is required.
2. **Proof and trust — pass as a decomposition.** Recompiled both modules in dependency order
   using `lcompile.py --all`, with no errors or warnings. The only delivered hole is the whole
   named theorem `AlgebraicGeometry.projectionComparison_exact`; no definition contains a
   hole, and no forbidden declaration or implementation attribute occurs. In a scratch copy,
   `#print axioms` for `projectionComparisonNatTrans`, `projectionComparison_exact`, and
   `projectionComparison_triangles` reported exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The natural transformation itself is constructed explicitly;
   its transitive `sorryAx` comes from imported foundations. The original theorem's proof
   eliminates existential shift structures only into a proposition and does not create a
   public data definition from an arbitrary unproved witness.
3. **Residual statement — pass, still open.** Read its signature, docstring, and node against
   Stacks Tag 08EU's exact-functor argument and the existing tensor, pullback and direct-image
   constructions. It asks for compatible exact shift structures on specified functors and
   a specified transformation, and contains no invertibility or isomorphism-locus conclusion;
   the supplied tensorator is not replaced by a canonical one. This is the geometric diagram
   step of the old argument, rather than a renamed copy of the target. Checked zero objects,
   zero and negative shifts, identity morphisms, and contractible triangles. Independent
   `msearch.py` searches used LeanFinder (exact functors/tensor/canonical mate), Loogle
   (`CategoryTheory.NatTrans.CommShift`), and grep (shift/mate/tensor-right exactness), plus
   `rg` through both library roots. The upstream tensor exactness, shift-comparison
   factorization lemmas, and `Adjunction.commShift_rightAdjointProjectionMap_app` require
   structures or factorization hypotheses not supplied here. Closing this residual is not
   a few-minute application of an existing theorem. Its representative-level proof and
   tensorator transport remain work for its eventual prover; they are not claimed formally
   established by this delivery.
4. **Reduction and pruning — pass.** Checked naturality of the explicit mate, conjugation
   along object isomorphisms, `NatTrans.app_shift`, all three triangle-morphism squares, and
   the direction of the final transport along `eC.symm`. The formal reduction uses Mathlib's
   two-out-of-three theorem directly. The retained public imports support the statement and
   its fixed structures; the added import is proof-only and used. No module is pruned. The
   six displaced direct proof dependencies are now explicitly listed above; they remain
   indirect dependencies through the residual. Read `sk-thm-picard-duality.json`: its
   realized statement and step lists contain no node at this location, and its unit route
   is unchanged.
5. **DAG agreement — pass after metadata repair.** Diffed the existing node: only `proof`,
   `proof_deps`, and `proof_origin` changed. Its steps match the implemented reduction.
   The new node records the statement dependencies, source, proof steps, their dependency
   union, origin, searches, creation, blueprint provenance, chapter, unit, and Lean record.
   Corrected its `lean.statement` to preserve the actual multiline Lean signature verbatim.

Second reading changed only the report and the new node's signature formatting: explicitly
listed all six displaced direct dependencies and documented this review. No Lean proof or
statement needed repair. Holes closed: `AlgebraicGeometry.projectionComparison_triangles`.
Holes added: `AlgebraicGeometry.projectionComparison_exact`. This remains one decomposition,
with zero net holes removed and no modules pruned.
