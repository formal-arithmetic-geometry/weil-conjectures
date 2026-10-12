## What changed

Proved AlgebraicGeometry.component_intersections_finite in
Sheaf.AlgebraicGeometry.ComponentIntersectionsFinite without changing its signature.
Distinct components cannot contain one another by maximality. Inside the first component,
the complement of the second is a nonempty open. The already proved source-library theorem
IsOpen.finite_compl_of_topologicalKrullDim_le_one proves finiteness of its complement;
IsOpen.isClosed_singleton_of_mem_compl proves closedness. Closed embeddings transfer closed
singletons to the scheme. Finite unions and the chosen irreducible component of each point
complete the assertion. Updated the docstring and the node proof to match this route.

## Proved and sorry left

Closed the sole hole: AlgebraicGeometry.component_intersections_finite
(lem-sc-component-intersections-finite). No holes added or split off, and none remain in
the delivered module. This is a complete proof, not a decomposition through new holes.
Local compilation passes without warnings; the delivery dry run also checks axioms and
preflight. Server compilation is deferred to the global batch build by the delivery tool.

## No longer needed

Removed import Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints and removed proof
dependency lem-sc-noetherian-closed-points-finite. Its theorem
AlgebraicGeometry.finite_of_isClosed_of_closed_points is unnecessary for this item.
Its supporting Mathlib finiteness argument is already implemented by the source library's
finite-complement theorem; the node now records
lem-sc-noetherian-closed-subset-finite-components for that argument.
All remaining imports are used. No other module is claimed to be globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned generic-point argument to show the difference of distinct components is
nonempty is unnecessary: maximality alone proves non-containment. The planned use of the
holed closed-points finiteness theorem also duplicates a proved source theorem.
The unit's route is preserved: this node is not itself a realized unit statement or step,
and it still proves precisely the finite intersection and uniqueness assertion of 09NX.
The empty scheme, zero-dimensional schemes, disjoint components and empty pairwise
intersections are included; nonemptiness is used only for an individual component's
complement of a distinct component. No hypotheses or definitions changed.

## Second reading by P2

1. PASS: compared the only delivered Lean module with the repository using diff, and
   independently extracted and compared its theorem signature byte for byte. No existing
   declaration statement or definition changed; no change record is needed. The only
   import removed is private to proofs.
2. PASS: compiled the module through lcompile.py without errors or warnings. A scratch copy
   with `#print axioms AlgebraicGeometry.component_intersections_finite` reports exactly
   propext, Classical.choice and Quot.sound, with no sorryAx. No sorry, axiom, unsafe,
   opaque, implemented_by or extern is introduced, and no data is chosen from an unproved
   existence statement.
3. PASS: no statements were split off, no new modules or nodes were added, and no holes
   remain. Checked the argument on empty schemes, singleton components, disjoint components
   and empty intersections: nonemptiness is required only for the difference of distinct
   maximal components, where maximality proves it.
4. PASS: read both upstream dimension-one theorems and searched the library and Mathlib
   topology sources for component-intersection and finite-complement results with alternative
   wordings. The existing finite-complement theorem supplies the short route; no additional
   lemma is needed. Both public Mathlib imports support the signature; the upstream import
   is proof-only. The sole removed old proof dependency is fully listed under No longer
   needed. The unit sk-thm-curveestimate realizes thm-sc-proper-cohomology and has no realized
   steps; this supporting node is not a realized unit statement or step, so the unit route
   remains intact.
5. PASS after documentation repair: read the changed node and the finite-component
   dependency. The node's proof and proof_deps match the maximality, finite-complement,
   closed-singleton, finite-union and component-cover arguments in Lean; the finite closed
   component decomposition is used inside the proved upstream theorem. proof_origin records
   the agent's shorter implementation of the cited Stacks argument. All other node fields
   are unchanged and no new-node requirements apply.

Changed during second reading: normalized over-escaped TeX in the node's proof text and
removed its stale claim that the generic-point non-containment argument was written out.
Corrected the report's server-compilation claim to describe the actual delivery-tool policy.
The Lean proof, declarations, imports and proof dependencies needed no repair.
