## What changed

Closed `AlgebraicGeometry.Scheme.perfect_bounded_coherent_cohomology` without changing
its signature, universes, visibility, definitions, or existing public imports.
All five private helpers are fully proved: finite presentation under the inverse
open-site equivalence, finite free presentation, finite presentation of retracts,
finite presentation of homology, and the local derived-cohomology comparison.
The proof uses the closed source-library kernel and cokernel theorems, gives an
explicit isomorphism from a retract to the kernel of its complementary projector,
and glues finite presentations before applying the Noetherian coherence criterion.
Compactness selects a finite subcover; symmetric bounds from the supremum of the
absolute values include the empty scheme automatically.

Added the proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`.
Updated the item's DAG proof and dependencies to this argument.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.perfect_bounded_coherent_cohomology`
(node `lem-pc-perfect-noetherian-cohomology`). No sorry remains in the item's
module, and the delivery adds zero holes. This is a proof, not a decomposition.
The new node records an existing closed source-library theorem; it introduces
no Lean declaration. Local compilation is clean and below the 60-second limit.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.CoherentModuleLocalOnOpenCover`
and its proof dependency `lem-weil-pbc-coherent-module-local-on-open-cover`.
This item no longer needs that module's descendants
`Sheaf.AlgebraicGeometry.CoherentKernelConditionRestriction`,
`Sheaf.AlgebraicGeometry.CoherentKernelConditionDescent`,
`Sheaf.AlgebraicGeometry.CoherentKernelConditionGluing`,
`Sheaf.AlgebraicGeometry.CoherentKernelIntersectionFiniteType`,
`Sheaf.AlgebraicGeometry.CoherentModuleFiniteTypeLocalCore`,
`Sheaf.AlgebraicGeometry.CoherentModuleFiniteTypeLocalRestrict`, and
`Sheaf.AlgebraicGeometry.CoherentModuleFiniteTypeLocalCover`.
Their nodes are `lem-weil-pbc-coherent-kernel-condition-restriction`,
`lem-weil-pbc-coherent-kernel-condition-descent`,
`lem-weil-pbc-coherent-kernel-condition-descent-local-generators`,
`lem-weil-pbc-coherent-kernel-intersection-finite-type`,
`lem-weil-pbc-coherent-module-finite-type-local-core`,
`lem-weil-pbc-coherent-module-finite-type-local-restrict`, and
`lem-weil-pbc-coherent-module-finite-type-local-cover`.
Eight Sheaf modules leave this item's import closure.
This is pruning from this proof; other targets may still use those modules.
Affine refinements, projective-term finite-free trivializations, and a separate
coherence descent argument are unnecessary. The existing finite-presentation
locality theorem does the required gluing. The second reading removed redundant direct imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` (available through the
cokernel import) and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (available
through `PerfectComplex` and `Coherent`). These two modules remain transitively
imported and are not additional closure pruning. Existing public imports were retained
for the declarations and instances used by the theorem signature.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically sound, but its affine refinement is unnecessary:
retracts are kernels of complementary projectors, so the existing closed
Noetherian kernel/cokernel theorems suffice. The source was checked at Stacks
Tag 0FXU, part (1), and Tag 01Y1. No false statement or interface fault was found.
The unit's `realized` arrays are empty; no unit statement or proof step is bypassed.
The existing Noetherian kernel node from another unit is used only as a closed
source-library tool; no replacement proof of that unit is undertaken.
Small cases include a rank-zero term, an empty open, an empty scheme, and bounds
of either sign. The sum of absolute bounds works without assuming a≤b.
The existing theorem docstring retains the original valid plan; the updated DAG
and this report give the implemented route.

## New nodes

`lem-pc-cokernel-finite-presentation-noetherian` attaches the already proved
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_cokernel` from
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`, lines 79–107.
Its exact general hypotheses allow a quasi-coherent source and a finitely
presented target on a locally Noetherian scheme. Repository search and blueprint
search found no node recording this exact source declaration. Mathlib searches
were actually run and logged: LeanSearch unavailable, LeanFinder returned only
finite-presentation definitions and instances, and grep returned no match.
No new module, theorem, sorry, or change record is introduced.


## Second reading by T2

1. **Interface: PASS.** Read the full module and its repository diff. The existing
   theorem `AlgebraicGeometry.Scheme.perfect_bounded_coherent_cohomology` has the
   identical signature, including both universes, derived-category instances,
   Noetherian hypothesis, perfectness hypothesis, bounds, and coherence conclusion.
   No existing definition or public import changed, and no other module is delivered.
   The five new declarations are private proved helpers, not interface changes.
   Read [Stacks 0FXU](https://stacks.math.columbia.edu/tag/0FXU), part (1): its
   bounded coherent derived-category conclusion agrees with the two Lean clauses.

2. **Proof: PASS.** Local compilation completed cleanly in 18.4 seconds; a scratch
   copy with `#print axioms` showed exactly `propext`, `Classical.choice`, and
   `Quot.sound` for the main theorem, with no `sorryAx`. Scanned the delivered
   source: no sorry, axiom declaration, unsafe, opaque, extern, or implemented_by.
   Read all five helpers. The complementary projector kernel isomorphism has
   both inverse identities proved. Homology is the cokernel of the incoming
   differential lifted into the outgoing kernel. The comparison explicitly
   composes restriction, derived homology, and complex homology isomorphisms.
   Chosen models and isomorphisms are local to a propositional proof; no data
   definition selects an arbitrary witness from an unproved existence theorem.

3. **Split statements and searches: PASS.** Zero statements are split off with
   sorry. The new node records the existing closed source theorem
   `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_cokernel`; read its
   full proof and compared every hypothesis with the node's Lean attachment.
   [Stacks 01Y1](https://stacks.math.columbia.edu/tag/01Y1) gives the quasi-coherent
   quotient clause; finite presentation/coherence on locally Noetherian schemes
   is the 01XZ criterion used by the source proof. Checked zero source, zero
   target, and empty opens: the quotient is still finitely presented. Searched
   DAG nodes for `isFinitePresentation_cokernel` and read
   `lem-weil-pbc-module-finite-presentation-cokernel`: it requires a finite-type
   source on a general ringed space, so does not duplicate the recorded theorem
   with an arbitrary quasi-coherent source on a locally Noetherian scheme.
   Independently ran Mathlib grep for homology/retract finite presentation and
   LeanFinder for finitely presented homology over Noetherian schemes; neither
   found a shorter sheaf-level theorem. Also searched Lean source for the same
   concepts. No restatement of the item or new unproved declaration is present.

4. **Route and pruning: PASS after import repair.** Checked top-down reduction
   to the closed source kernel/cokernel results, finite-presentation gluing, and
   the proved Noetherian coherence criterion. No affine refinement is needed.
   Rank-zero free modules and retracts are covered by the zero-relations
   presentation. Symmetric bounds dominate either sign of local bounds, without
   assuming their order; on the empty scheme the finite cover and its supremum
   are empty, giving bounds zero. The only old proof dependency removed is
   `lem-weil-pbc-coherent-module-local-on-open-cover`, named above with its
   descendants. Read `dag/units/sk-thm-picard-duality.json`: its realized statement
   and step arrays are empty; this reduction bypasses no realized unit node.
   Removed two redundant proof imports and compiled a scratch copy without
   both cleanly in 13.9 seconds. The source cokernel import and the coherence
   criterion import remain needed for their declarations.

5. **DAG: PASS.** Compared the existing node with its repository version: only
   `proof`, `proof_deps`, and `proof_origin` differ. Each step names precisely the
   used definition or kernel/cokernel/coherence result; proof_deps is their union.
   Read the new node's statement, source, search records, provenance, chapter,
   unit, and existing Lean attachment: it adds no module or proof hole, and its
   statement is the source theorem verbatim in the Lean record. No change record
   is needed because no signature or definition changed.

Changed only the two redundant proof imports and this report. The mathematical
proof and DAG records were retained. Closed one existing hole, added zero holes.
