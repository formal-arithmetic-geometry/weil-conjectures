## What changed

Proved `AlgebraicGeometry.projectionFormula_local_to_global` in
`Sheaf.AlgebraicGeometry.ProjectionFormulaLocalityLocalToGlobal` by applying
`DerivedCategory.isIso_iff`, the proved exact-functor cohomology comparison, and
`AlgebraicGeometry.sheaf_module_isIso_iff_isIso_over_open_cover`.
Added a proof-only import of `Sheaf.Topology.SheafIsomorphismLocalOpenCover`.
Updated the existing node's proof, proof dependencies, and proof origin to match.
The theorem's signature and all public imports are unchanged.

## Proved and sorry left

Proved the item's only previously sorry declaration:
`AlgebraicGeometry.projectionFormula_local_to_global`
(node `lem-pc-projection-locality-local-to-global`). No sorry remains in the item,
and no new sorry was added. The proof uses the existing named theorem
`AlgebraicGeometry.sheaf_module_isIso_iff_isIso_over_open_cover`
(node `lem-weil-pbc-sheaf-isomorphism-local-open-cover`), whose proof still has
sorry in the current library. This is the next required item, not a new split.

Local compilation passes without warnings. The proof applies to every morphism
of the displayed type, without using quasi-compactness, quasi-separatedness, or
the construction of the projection map. It handles an empty cover of the empty
scheme as well: the sheaf locality theorem includes that case.

## No longer needed

No original imports, nodes, or modules were removed. A redundant temporary
proof import of `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` was
removed because the public derived-category interface already provides it.
No projection-formula compatibility, restricted-morphism base change, or
boundedness results are required for this local-to-global direction.

## Where the brief, the DAG or earlier work was wrong

The node had no proof dependencies and its single step repeated its conclusion.
The updated proof specifies the cohomology argument and the existing module
sheaf locality dependency. The latter is used as a generic tool from another
unit, without changing this unit's statement or route. No unit realization is
bypassed (the assigned node is not in the unit's realized fields).
The existing theorem statement and definitions were usable unchanged.

## Second reading by M1

1. **Statements and interfaces.** I compared the delivered theorem with the repository
   version byte for byte at its declaration: its hypotheses, universes, morphism, and
   conclusion are unchanged. The three cited proof dependencies have the interfaces used
   in the proof: the derived-category homology criterion, the exact-functor homology
   comparison, and module-sheaf locality on an open cover. No target statement or
   definition changed.

2. **Proof validity.** The delivered module compiles cleanly with the launcher compiler.
   The proof reduces invertibility to all homology maps, transports each local derived
   isomorphism through the exact restriction comparison, reflects through the module
   equivalence, and applies the open-cover criterion. It contains no `sorry`, axiom,
   unsafe, opaque, extern, or implemented-by declaration.

3. **Split statements and nodes.** No statement was split off and no new node was added.
   The existing locality theorem is used as a strictly smaller tool; it is not a
   restatement of this projection-formula theorem. Its empty-index edge case is only
   applicable when the covered scheme is empty, and the proof handles it through the
   stated cover equality.

4. **Pruning and imports.** The only added import is the proof-only
   `Sheaf.Topology.SheafIsomorphismLocalOpenCover`; all public imports remain unchanged.
   The proof does not use the temporary homology-sequence import or any projection
   compatibility, boundedness, or base-change result. The unit route is preserved: this
   node is not listed in the unit's realized statement or step fields.

5. **DAG agreement and axioms.** The node's proof steps, proof dependencies, and
   proof origin now describe the Lean proof and agree with its declarations. The local
   axiom probe and compilation pass; the proof introduces no axioms beyond Lean's
   permitted standard axioms.

I changed only the proof-only import, the theorem proof, and the node's proof metadata;
the theorem signature and public interface remain unchanged.
