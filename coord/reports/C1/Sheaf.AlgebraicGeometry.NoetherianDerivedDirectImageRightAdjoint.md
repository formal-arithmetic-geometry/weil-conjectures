## What changed

Proved `AlgebraicGeometry.noetherian_schemeDerivedDirectImage_has_rightAdjoint` in
`Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint` by specializing the
existing, more general `AlgebraicGeometry.schemeDerivedDirectImage_qcqs_hasRightAdjoint`.
Mathlib infers quasi-separatedness of both schemes from local Noetherianness, then
quasi-compactness and quasi-separatedness of the morphism. The preservation witness
is restricted to full-subcategory objects by applying it to `E.obj` and `E.property`;
the supplied adjoint witness then has the required type definitionally.

Added the proof-only import `Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint`.
Updated the item's DAG proof, proof dependencies and proof origin to match this route.
No statement, definition, public import or universe changed. The unit's `realized`
statement and steps are empty, and no unit realization is bypassed.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.noetherian_schemeDerivedDirectImage_has_rightAdjoint`
(node `lem-pc-noetherian-derived-direct-image-right-adjoint`). No sorry remains in the
item and no new sorry is added. Its proof still depends on the existing general theorem
`AlgebraicGeometry.schemeDerivedDirectImage_qcqs_hasRightAdjoint`
(node `lem-pc-qcqs-derived-direct-image-right-adjoint`), whose proof is currently sorry.
This is a proof from an existing declaration, as required by stage 3, not an axiom-free
closure of the target's dependency tree.

Local single-file compilation passed with no errors or warnings.

## No longer needed

Removed these direct proof imports and corresponding direct DAG dependencies:

- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums`
  (`lem-pc-derived-direct-image-preserves-direct-sums`).
- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`
  (`lem-pc-derived-direct-image-preserves-qcoh`).
- `Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration`
  (`lem-pc-derived-qcoh-compact-generation`).
- `Sheaf.AlgebraicGeometry.DerivedQCohDirectSums`
  (`lem-pc-derived-qcoh-direct-sums`).
- `Sheaf.CategoryTheory.BrownRepresentabilityRightAdjoint`
  (`lem-pc-brown-representability-right-adjoint`).

These remain dependencies of the general qcqs theorem. They are pruned from this
module's direct argument, not declared unnecessary to the whole project. The geometric
Mathlib dependencies `lem-weil-pbc-locally-noetherian-quasi-separated` and
`lem-weil-pbc-qcqs-morphism-permanence` remain, along with the general qcqs node.

## Where the brief, the DAG or earlier work was wrong

The original plan duplicated the Brown-representability argument already encapsulated
by the existing qcqs right-adjoint theorem in the same unit. That theorem's hypotheses
follow directly from the item's Noetherian hypotheses; its conclusion differs only in
how the preservation witness is indexed. No mathematical statement was found wrong.
The second reader updated the existing docstring to describe the actual specialization;
the sandbox DAG records that same route.

Searches: Lean Finder returned ordinary sheaf pushforward adjunctions, not this derived
left-adjoint result. Loogle reported an unknown identifier for `Functor.IsLeftAdjoint`;
that is a parser failure, not evidence of absence. Local `rg` found the existing qcqs
module and its signature; the prescribed grep search returned no hits. The import
cycle check accepted the new proof-only import. No new nodes were needed.


## Second reading by C1

1. **Interface: PASS.** Compared the sole delivered Lean module with the repository
   using `diff`, and separately compared the theorem signature byte for byte. The
   signature, universes, definitions and public imports are unchanged. No change record
   is needed. Only the proof, proof-only imports and proof documentation change.
2. **Proof: PASS, with an existing open dependency.** The module compiled locally
   without warnings or errors. A scratch copy with `#print axioms` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected
   from the existing qcqs theorem and the open definitions it uses; this delivery
   claims local proof closure, not closure of the dependency tree. No `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` is added or left in
   the delivered module. The supplied adjoint witness applies to exactly the lift
   determined by the restricted preservation witness.
3. **Split statements: PASS (none).** No new theorem, node, or split-off `sorry`
   is delivered. Read the existing qcqs theorem: it genuinely applies to all qcqs
   schemes and morphisms, not just Noetherian ones. The specialization also covers
   empty schemes and identity morphisms, with no extra nonemptiness or separation
   hypothesis. Independent local searches of Mathlib and the upstream geometry
   files found ordinary sheaf adjunctions only; the prescribed grep query
   `pushforward.*IsLeftAdjoint|IsLeftAdjoint.*pushforward|derived.*adjoint` returned
   12 ordinary sheaf hits and no replacement for the derived qcqs theorem.
4. **Route and pruning: PASS.** The two-line specialization is the shortest available
   route. Checked Mathlib's locally-Noetherian quasi-separatedness and the two qcqs
   morphism instances against the inferred hypotheses. The five old direct proof
   dependencies not used here are all listed under `No longer needed`; they remain
   beneath the general theorem. The three public imports support the unchanged
   signature; the new import is proof-only. The unit record
   `sk-thm-picard-duality` has no realized statement or step nodes, and the same-unit
   qcqs theorem retains the Brown argument; no unit realization is bypassed.
5. **Nodes: PASS.** Compared the existing node JSON with the repository: only
   `proof`, `proof_deps`, and `proof_origin` differ. The union of step `uses` equals
   `proof_deps`, and all three dependencies match the typeclass reductions and
   theorem application in Lean. No new-node fields are required.

Second-reading repair: updated the theorem's proof docstring from the obsolete
six-step direct Brown argument to the actual qcqs specialization and preservation
witness restriction. The Lean proof and node route required no repair.
