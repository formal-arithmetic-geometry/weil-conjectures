## What changed

The target theorem is proved by the arrow-level theorem. The arrow-level proof now composes
three explicit constructions: K-flat derived tensor computation, the ordinary closed-immersion
projection comparison, and exact pushforward on homology. These are supplied by the new helper
modules `KFlatSingleTensorRepresentative`, `ClosedStructureTensorProjection`, and
`ClosedStructureTensorComplexProjection`.

## Proved and sorry left

Proved `exists_selfTor_projection_homology_termwise_arrow` and
`nonempty_selfTor_projection_homology_termwise`. Proved
`nonempty_kFlat_single_tensor_representative` and
`nonempty_closedStructure_tensor_complex_projection`. Closed one original hole and added one strictly lower hole (net zero: a decomposition).
The only remaining sorry is
`nonempty_closedStructure_tensor_projection`, in node
`lem-pc-closed-structure-tensor-projection`; it is the strictly smaller natural ordinary
projection formula for a closed immersion, used to build the complex comparison.

## No longer needed

No public imports were removed: all four original imports support the unchanged signatures.
The arrow node no longer needs `lem-pc-qcqs-derived-projection-iso-universes`,
`lem-sc-closed-immersion-pushforward-exact`, or `def-pc-derived-pullback` as proof
 dependencies. Their modules `Sheaf.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses`,
`Sheaf.Topology.ClosedImmersionPushforwardExact`, and `Sheaf.AlgebraicGeometry.DerivedPullback`
are not imported by this proof. The module-valued exactness theorem
`closed_modulePushforward_preservesHomology` supplies the final step directly.
These are pruned from this argument only; they may still be reached elsewhere.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt treated the arrow theorem as an unavoidable remaining hole. The source
library already provides the derived K-flat model and homological-complex comparison APIs;
a natural ordinary projection formula is the only missing intermediate statement. The arrow-versus-isomorphism packaging in the
previous attempt did not reduce the argument. The new ordinary functor theorem has no
K-flat resolution, derived category, augmentation, or homology degree in its statement.
Checked edge cases: identity immersion gives tensor with the unit; empty source gives zero;
arbitrary unbounded complexes are treated termwise; no flatness of i is needed.
All four modules compiled without warnings using lcompile.py. The K-flat module uses
only the standard category axioms and existing tensor construction dependencies.
No data is chosen from the remaining mere-existence theorem inside a definition: both
consumers are theorem proofs. No existing signatures, definitions, or visibility changed.

## New nodes

Added `lem-pc-kflat-single-tensor-representative`,
`lem-pc-closed-structure-tensor-projection`, and
`lem-pc-closed-structure-tensor-complex-projection` with corresponding modules. The ordinary
projection node remains split with its proof deferred; its statement is strictly below the
arrow-level theorem.


## Second reading by S1

1. Compared the delivered target module against the repository version. Existing theorem signatures and definitions are byte-for-byte unchanged; only proof text, proof-only imports, and documentation changed. Verdict: pass.

2. Compiled all four delivered modules with `lcompile.py` in dependency order. There are no forbidden declarations and the only remaining `sorry` is the named split theorem `nonempty_closedStructure_tensor_projection`. Axiom checks on the proved helper declarations use only the permitted axioms; the target proofs inherit `sorryAx` solely through that explicitly split theorem. Verdict: pass.

3. Checked the three added statements against their DAG nodes and source. The K-flat representative and complex projection statements are strictly below the target and are needed by the arrow proof; the ordinary projection statement is the single strictly lower unresolved hole, with an explicit source and proof docstring. Edge cases are addressed in the docstrings. Verdict: pass.

4. The proof follows the shortest available route through the existing K-flat, complex comparison, and exact pushforward APIs. The target proof dependencies and imports were pruned to the declarations actually used; the unit route remains represented by the arrow and termwise nodes. Verdict: pass.

5. DAG nodes and Lean declarations agree, including proof steps, dependencies, origin, and split status. Verdict: pass.

Changed only the target proof/documentation and added the three helper modules and matching DAG nodes already described above. No further repair was necessary.
