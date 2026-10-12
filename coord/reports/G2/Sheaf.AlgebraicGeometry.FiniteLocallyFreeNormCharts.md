## What changed

Proved `AlgebraicGeometry.exists_finiteLocallyFree_norm_charts` with its signature and
visibility unchanged. Added five proved private helpers in the same module: scalar
extension of norms, restriction to affine subopens, restriction of a section from W,
compatibility on chart overlaps, and existence of finite free affine charts.

The local charts use the already proved
`Scheme.Modules.isFiniteLocallyFree_pushforward`, `exists_mem_over_iso_free`, and
`sectionsLinearEquivOfOverIsoFree`. Norm restriction uses the affine section-ring
pushout, `Algebra.norm_eq_of_algEquiv`, `Algebra.baseChange_lmul`, and
`LinearMap.det_baseChange`. Sheaf separatedness and unique gluing complete the proof.
The source read was Stacks Project Tag 03JE (groupoids-lemma-find-invariant-affine),
its norm paragraph. Updated the existing node's proof, proof_deps, and proof_origin
to describe this implementation. The existing theorem docstring is preserved.

Added only proof imports of `WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward`,
and `Mathlib.RingTheory.Norm.Basic`.
No definitions, public imports, public signatures, or other modules were changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_finiteLocallyFree_norm_charts`
(node `lem-pd-finite-locally-free-norm-charts`). All five private helpers are proved.
No sorry remains in the delivered module, and no holes or new modules were added.

The proof handles empty W via the empty indexed cover. Empty inverse images and rank
zero cause no exceptional case in determinant base change; varying ranks are allowed
because each chart is separately trivialized. Overlaps are covered by affine opens
and are never assumed affine. No data is selected from an unproved existence theorem.

Validation: the prescribed single-file compiler succeeds without warnings. The delivery
wrapper additionally checks every declaration's axioms and performs the dry-run preflight.

## No longer needed

No original import or project module was pruned. The second reader removed the redundant
proof import `Mathlib.LinearAlgebra.Charpoly.BaseChange`: the determinant base-change
lemma is already available through the remaining imports (verified by compilation).
Removed the redundant trial proof
imports `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine` and
`Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`; their declarations are already
available through the necessary FinitePushforward import. The original node's
`def-pc-finite-locally-free` is no longer a proof dependency (it remains a statement
dependency, and its source module remains transitively imported).

The proof does not use `Algebra.norm_localization`, a common principal-open refinement,
or a new free-localization argument: the proved pushforward theorem gives charts and
determinant base change gives restriction on arbitrary affine subopens. These were
planned arguments, not separately imported nodes, so no reachable module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG's two steps named only definition nodes, not the available proved
finite-flat pushforward theorem. That theorem closes the chart-existence step directly.
The proposed simultaneous principal-open localization is unnecessary: affine section
algebras form the required pushout and determinants commute with scalar extension.
No statement error or change of the unit's route was found. The unit's realized lists
are empty; the local-chart and gluing steps of this node are both retained.


## Second reading by G2

1. PASS: compared the complete module diff with the repository. The existing theorem
   signature is byte for byte unchanged, as are all original public imports and
   visibility. There are no definition changes or changed statements. Restored the
   original theorem docstring; the implementation route remains documented above and
   in the node. No change record is required.
2. PASS: the prescribed local compiler succeeds without warnings. A scratch copy with
   `#print axioms` for the main theorem and all five private helpers shows exactly
   `propext`, `Classical.choice`, and `Quot.sound` for each. No `sorry`, forbidden
   declaration, or unproved witness selection occurs. Chart choices and gluing use
   proved existence theorems.
3. PASS: there are no split-off statements, added holes, or new public declarations.
   The private helpers are genuine proved steps. Checked empty W (empty indexed
   cover), empty inverse images and rank zero (determinant scalar extension), arbitrary
   varying ranks, and nonaffine overlaps (affine basis cover). Independent LeanFinder
   search for scalar extension of determinant norms and Loogle search for
   `Algebra.norm, TensorProduct.tmul` found no shorter norm theorem. Repository search
   found `BaseChangeNorm.normAt_map_of_eq_basicOpen`, which only covers basic opens
   for finite field-extension pullbacks and cannot replace this general argument.
4. PASS: reviewed the proof from the target down through gluing, overlap equality,
   affine restriction, determinant base change, and chart existence. The available
   proved finite-flat pushforward theorem supplies charts directly. Checked the
   Stacks Tag 03JE norm paragraph and the unit `sk-prop-jacobian-descent`; no realized
   unit statement or step is bypassed (its realized lists are empty). Both chart
   construction and norm gluing remain. Tested removing each added proof import in
   scratch copies: FinitePushforward and Norm.Basic are necessary, while
   Charpoly.BaseChange is redundant and was removed. The no-longer-needed dependency
   `def-pc-finite-locally-free` is fully recorded above; no module pruning is claimed.
5. PASS: the node statement, statement dependencies, Lean signature, and other
   interface fields are unchanged. Its three proof steps match the helpers and main
   proof; proof_deps is exactly their uses union, namely the proved finite-flat
   pushforward node and def-pc-scheme. The cited pushforward node matches the actual
   theorem and is audited closed. The updated proof_origin accurately states the
   determinant scalar-extension implementation. No new nodes need validation.

Changes by the second reader: removed one redundant proof import, restored the
original public theorem docstring, and corrected this report accordingly. No proof
body or signature changed. Closed one original hole; added zero holes.
