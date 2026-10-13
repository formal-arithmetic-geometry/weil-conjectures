## What changed

Replaced the `sorry` in `AlgebraicGeometry.derived_open_gluing_objects` by the
homotopy-fiber argument of Stacks Project Tag 08DG. The theorem's signature and
existing docstring are unchanged. Added the fully proved private helper
`AlgebraicGeometry.isIso_fiber_projection`: TR3 maps a distinguished triangle to
the binary biproduct triangle, and the two-isomorphism lemma proves that its
fiber projection is invertible. Added the fully proved private helper
`AlgebraicGeometry.compatible_of_difference` for the generic naturality/zero-composite
calculation; specializing it avoids expensive repeated unfolding of scheme comparisons.

Added `Sheaf.AlgebraicGeometry.DerivedOpenDifferenceDiagram` with the strictly
pre-triangle construction `AlgebraicGeometry.derived_open_difference_diagram`.
Its objects are fixed to E=RjU_*A⊕RjV_*B and D=RjW_*(sV B). It produces
only the difference arrow, the two projections, an overlap factorization,
and invertible local block maps. It does not produce a glued object or any
isomorphism from a restricted glued object. The original module constructs the
fiber, proves its projections invertible, and derives its prescribed transition
from naturality and the zero composite in its distinguished triangle. This is a
decomposition following the existing cone route, not a complete axiom-free proof.

Reused `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps` for the exact
restriction functors and the existing canonical comparison. Converted the goal
to these named expressions before eliminating existentials, avoiding repeated
elaboration of the large expanded comparison terms. Kept the original namespace-opening commands and local instance rules unchanged. The only new import in the existing
module is the private proof import of the new diagram module; its public imports remain unchanged.

Updated `lem-sc-derived-open-gluing-objects` in the sandbox to describe the actual
Lean argument and its direct dependencies. No definitions, existing signatures,
targets, or other held modules were changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.derived_open_gluing_objects`
(`lem-sc-derived-open-gluing-objects`). Its proof is complete from the new
pre-triangle diagram theorem. The private `AlgebraicGeometry.isIso_fiber_projection` and
`AlgebraicGeometry.compatible_of_difference` are proved with no `sorry`.

Added one remaining hole:
`AlgebraicGeometry.derived_open_difference_diagram`
(`lem-sc-derived-open-difference-diagram`), in its own new module. Its entire proof
is `:= by sorry`, with source and a complete construction/matrix argument in its
docstring and node. No `sorry` remains in the original module. Holes closed: 1;
holes added: 1; net: 0. This is a decomposition, not a net reduction in holes.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` from the original
module. Its declaration/node `lem-pc-restrict-derived-direct-image-open` remains
needed for proving the new diagram theorem; it has not been globally pruned.
There are no unused imports in the delivered modules, and no entire planned
nodes or modules are claimed to be globally unnecessary. The original two-step
cone route and the existing abstract derived-category Mathlib leaf are retained.

## Where the brief, the DAG or earlier work was wrong

The recorded Tag 08FE declaration gives `Nonempty` of a functor isomorphism,
without the counit/adjunction compatibility equations or local matrix normal
forms required by this proof. Its signature alone therefore cannot directly
supply the entire difference diagram. The new node makes this missing portion
explicit; it does not assert that the existing restriction theorem is false.

The full source checkout's Stacks `cohomology.tex` is not present in this clone.
Read the primary source at https://stacks.math.columbia.edu/tag/08DG instead;
the source reference in the project node remains the canonical literature path.
Mathlib searches used LeanFinder, Loogle, and grep; LeanSearch returned an
Internal Server Error. No exact pre-triangle diagram theorem was found.

Checked the new statement's edge cases: U=V=X gives d=(c,-1) on A⊕B, and both
block maps are invertible; if the intersection is empty the pushforward from
it is zero and the block maps reduce to identities. Empty U or V likewise
removes a zero summand. No quasi-coherence, compactness, boundedness or
nonemptiness assumption has been added. The unit's `realized` arrays do not
mark this node as its statement or a proof step, and the existing cone route
is kept unchanged.

## New nodes

`lem-sc-derived-open-difference-diagram`, in
`dag/nodes/sec-picard-framework/lem-sc-derived-open-difference-diagram.json`,
states the difference diagram before choosing its homotopy fiber. Its source is
Tag 08DG's difference-arrow construction and Tag 08FE's restricted direct images.
Its proof has the adjunction/factorization step and the two local matrix steps.
It inherits the original node's chapter/unit and has all three search records.
It is strictly a part of the argument: the middle and last objects are fixed
explicit direct-image constructions; the nontrivial fiber construction,
TR3/five-lemma calculation and transition deduction are already proved in Lean
in the original module. Final local compilation is clean (both files under the
60-second limit).
The original signature/public-import comparison was checked mechanically.
No change record is required for existing interfaces,
since none changed; no forced adaptations were made.

## Second reading by S2

1. **Interfaces: pass.** Compared both delivered modules and both node files with
   the repository. The existing theorem signature is byte-for-byte identical;
   its docstring, namespace openings, local instance rules and public import are
   unchanged. The only existing Lean edits are the proof, two private proved
   helpers and a private proof-import replacement. No definition or target was
   altered; no change record or forced adaptation is needed.
2. **Proof and axioms: pass as a decomposition.** Independently compiled both
   modules with lcompile.py (7.7 and 42.8 seconds). A scratch copy with explicit
   #print axioms checks compiled in 34.9 seconds: both private helpers use only
   propext, Classical.choice and Quot.sound; the main theorem and the diagram
   theorem additionally use sorryAx. Scanned all delivered Lean: the only sorry
   is the named diagram theorem; there are no forbidden declarations or hollow
   definitions. The existential diagram is eliminated inside a theorem proof,
   not used to choose arbitrary data for a public definition.
3. **Split statement: pass.** Read the precise canonical restriction comparisons,
   Tag 08DG (https://stacks.math.columbia.edu/tag/08DG) and Tag 08FE
   (https://stacks.math.columbia.edu/tag/08FE). The fixed E and D and their local
   block maps are the part of the construction before the triangle; the remaining
   triangle, TR3, isomorphism and transition arguments are real Lean proofs, so
   this is not a renaming of the original existence assertion. For U=V=X the
   arrow is (c,-1), and both projection/difference matrices are invertible. For
   disjoint opens D is zero; for an empty open the corresponding category is
   zero. These checks add no extra hypotheses. Repeated LeanFinder, Loogle and
   grep searches with triangulated-gluing and biproduct-isomorphism vocabulary;
   no duplicate difference-diagram theorem was found. Inspected derived
   Mayer--Vietoris, perfect-gluing presentations and supported-open comparisons:
   they require a pre-existing global object, perfectness, quasi-coherence or
   support assumptions and do not replace this general construction. Closing
   the diagram requires the canonical adjunction/base-change compatibility and
   matrix calculations; it is not a short missing tactic proof.
4. **Route and pruning: pass.** Checked the two private helpers from their
   conclusions downward: the first uses Mathlib's distinguished biproduct
   triangle and two-isomorphism lemma, the second uses naturality and subtraction.
   The original two-step cone route remains. The unit's realized statement and
   step arrays are empty and unchanged. The removed direct proof import and its
   old dependency are explicitly named in No longer needed; that dependency is
   still needed below the new diagram and is not claimed globally pruned.
   The public import of the new module supplies its statement's restrictions,
   direct images and comparisons; the original module imports it privately for
   its proof. No additional import can be removed without losing required names.
5. **DAG: pass.** The existing node records the new diagram, triangle completion,
   fiber projection and transition calculation and their actual dependencies.
   The new node has its source, complete proof plan, statement dependencies,
   proof dependencies, search records, provenance, blueprint, chapter/unit and
   verbatim Lean statement. Exactly one original hole is closed and one lower
   hole is added: net zero, expressly a decomposition rather than an axiom-free
   result.

Second-reading changes: clarified the new diagram docstring's V-side matrix
entry as the direct image of c, rather than c itself; added the independently
checked Loogle search record to the new node; appended this review. No Lean
statement, definition or proof was changed.
