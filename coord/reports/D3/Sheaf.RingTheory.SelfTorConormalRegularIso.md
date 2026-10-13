## What changed

Completed the proof of `AlgebraicGeometry.selfTorConormalComparison_isIso`. The proof
uses the conormal basis, the normalized Koszul projective resolution, the quotient tensor
homology basis, and `selfTorConormalComparison_spec`; it identifies the comparison after
composition with two isomorphisms and cancels the latter. The two proof support modules
remain included and compile with complete proofs. Existing statement imports are unchanged;
the support imports are proof-only. The normalized resolution now reuses the existing
private degree-one calculation via `import all`, replacing its duplicate proof.

## Proved and sorry left

The assigned declaration `AlgebraicGeometry.selfTorConormalComparison_isIso` is proved
without `sorry`. The support declarations
`ExteriorAlgebra.exists_koszul_normalized_projective_resolution` and
`AlgebraicGeometry.exists_koszul_quotient_tensor_homology_basis` are also proved without
`sorry`. No new `sorry` is introduced. The existing imported hole
`AlgebraicGeometry.existsUnique_selfTor_conormal_comparison`
(node `new-r4-self-tor-conormal-comparison`) remains upstream and is used only through
its public specification. Holes closed in the assigned module: 1 of 1. Holes added: 0.

## No longer needed

Removed the duplicate private declaration
`ExteriorAlgebra.koszulBoundary_zero_quotient_formula` from the normalized resolution
module. The proof now reuses the existing private theorem through
`import all Sheaf.RingTheory.KoszulProjectiveResolution`; that module and its node
`new-j3-koszul-projective-resolution` remain needed and are not pruned.
Removed direct proof imports `Mathlib.LinearAlgebra.ExteriorPower.Basis` and
`Mathlib.Algebra.Category.ModuleCat.Projective` from the normalized resolution module:
the existing resolution module supplies them. Replaced the item's old direct dependency `new-j3-koszul-projective-resolution`
with `new-d3-koszul-normalized-projective-resolution`; the old node remains
transitively needed through the reused degree-one helper, so its module is not pruned.
Second reading removed the duplicate private
`AlgebraicGeometry.koszulBoundary_wedge` from the tensor-homology support module.
The proof now uses `ExteriorAlgebra.koszulBoundary_wedge` through proof-only
`import all Sheaf.RingTheory.KoszulBaseChangeIso` (node
`lem-sc-koszul-base-change-iso`). This import also supplies the tensor basis machinery,
so the direct proof import `Mathlib.LinearAlgebra.TensorProduct.Basis` was removed.
No DAG nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

Repair of the return after reviewer X-fcce5: landing rejected the duplicate private
`ExteriorAlgebra.koszulBoundary_zero_quotient_formula`. The existing helper is accessible
via Lean's proof-only `import all`, so the repair deletes its duplicate proof and reuses
the existing theorem without changing any library signature or visibility. The normalized
resolution still supplies the augmentation equation absent from the old existence theorem.
Its node now records the reused helper's existing node as a proof dependency.
The earlier report incorrectly declared the old resolution module pruned; corrected above.

## New nodes

`new-d3-koszul-normalized-projective-resolution` and
`new-d3-koszul-quotient-tensor-homology-basis` are the two support nodes already present in
the sandbox, each with a complete proof and matching DAG record.

The required change record is `coord/changes/selfTorConormalComparison_isIso.md`.

## Second reading by D3

1. Compared the assigned module with the repository version using `diff -u`.
   Its existing declaration signature and docstring are byte for byte unchanged;
   changes are the proof, three proof-only imports, and the recorded namespace opening.
   The two support modules are new, with signatures matching their node records.
   No existing definition or public import was altered. Verdict: pass.
2. Read all three proofs and compiled the set locally in import order. No delivered
   file contains `sorry`, forbidden declarations, or hollow definitions. The resolution
   and homology isomorphism are constructed in their proofs; the only selected upstream
   data relevant here is the comparison determined uniquely by its normalization.
   Axiom probes show only `propext`, `Classical.choice`, and `Quot.sound` for both
   support results; the target additionally has `sorryAx` from its reported upstream
   comparison hole. Verdict: pass, with
   the upstream unique-comparison hole explicitly retained in the report.
3. No unproved statements were split off. The normalized resolution fixes the
   augmentation that the old existence statement does not fix; the other support
   result calculates quotient-tensor homology without assuming regularity. Both are
   strictly intermediate results, fully proved, with docstring arguments and nodes.
   Checked n=0, n>r, r=0, and the zero quotient: exterior bases and zero differentials
   handle all four cases without a nontriviality or properness assumption. Independent
   grep, LeanFinder and Loogle searches found generic homology/resolution primitives,
   already used here, rather than a ready-made normalized comparison theorem.
   Library search found the duplicate private wedge formula; repaired it. Verdict: pass.
4. Read the proof from the assigned theorem down. It uses the conormal basis,
   normalized resolution, quotient homology basis, and comparison specification,
   then extends equality by basis expansion and cancels an isomorphism. The old
   resolution alone does not give the augmentation equality the specification needs.
   Checked `dag/units/sk-thm-picard-duality.json`: its realized arrays are empty and
   unchanged; this local calculation bypasses no realized unit statement or step.
   The old direct dependency remains transitively needed, as documented above.
   Support imports have statement/proof visibility appropriate to their uses.
   Verdict: pass after removing the duplicate helper and redundant tensor-basis import.
5. Checked the target and both support nodes: Lean signatures match, proof steps
   describe the actual constructions, and proof dependencies are the union of the
   cited step dependencies. Added `lem-sc-koszul-base-change-iso` to the homology
   node to record the reused private helper. New-node provenance, source, searches,
   blueprint, chapter, unit, and Lean records are present. Verdict: pass after repair.

Second-reading changes: reused the existing private standard-wedge boundary formula,
removed its duplicate proof and the now-redundant direct tensor-basis import, updated
that support node's proof/dependency record, and clarified the retained old dependency
and review findings in this report. No signatures or mathematical statements changed.
