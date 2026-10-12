## What changed

Replaced the single sorry in
`AlgebraicGeometry.IsCurve.dense_open_cohomology_finiteness` by a complete Lean reduction.
The declaration's signature and existing docstring are unchanged. The proof constructs the
reduced closed complement via its vanishing ideal, forms the existing module-valued
open–closed short complex, and uses the source library's proved `shortExact_map_forget₂`
to obtain the abelian short exact sequence. Degree zero transfers by injectivity.
Every positive degree transfers using the connecting map and exactness; the reverse
implication uses exactness at the middle term in every degree.

The private, fully proved helper `finite_middle_of_exact` applies Mathlib's
`AddGroup.fintypeOfKerEqRange` to an exact pair with finite outer groups. There is no
axiom, partial proof, changed target, or new definition.

Added proof-only imports of `WeilConjectures.SixFunctors.OpenClosed.Exact`,
`WeilConjectures.SixFunctors.Etale.Gabber` (for its already proved coefficient-forgetting
lemma and additive instance), `Mathlib.GroupTheory.QuotientGroup.Finite`, and the new
`Sheaf.AlgebraicGeometry.Curve.DenseOpenBoundaryCohomology`.

The boundary theorem isolates the geometric part: the canonical closed-boundary sheaf
has finite H^0 and zero positive cohomology. It does not state any finiteness equivalence
between F and its extension by zero. Its complete proof in words follows the closed-boundary
paragraph of Stacks Tag 0GJA, read at https://stacks.math.columbia.edu/tag/0GJA.
The local Stacks source checkout is absent; the online source was read without writing to
the repository. The unit's dense-open localization route is kept.

Both modules compile together, without errors or warnings, using the required lcompile.py.
The item's proof also compiles without any transparency option. Updated the item's DAG proof,
proof_deps and proof_origin to match the uniform exact-sequence argument.

## Proved and sorry left

Proved, from the stated boundary theorem and the already proved exact-sequence machinery:
`AlgebraicGeometry.IsCurve.dense_open_cohomology_finiteness`
(node `lem-pbc-a3-dense-open-cohomology-finiteness`).
Also proved the private algebraic helper `finite_middle_of_exact`.
There is no sorry in the item's module.

The delivery leaves exactly one sorry:
`AlgebraicGeometry.IsCurve.dense_open_boundary_cohomology`, in its own new module,
node `lem-pbc-g2-dense-open-boundary-cohomology`.
It is strictly the closed-boundary calculation, not a restatement of the item.
Its statements allow empty X, U = X, zero-dimensional X, and the zero coefficient ring.
For U = X the boundary sheaf is zero and H^0 is the one-element group; for zero-dimensional
X a dense open is all of X. All hypotheses of the original declaration are preserved.

## No longer needed

No pre-existing public import was removed: each is used by the unchanged statement.
The attempted proof-only import of `DenseOpenHighCohomology` was removed.
The final proof needs none of:

- `lem-pbc-s2-dense-open-high-cohomology`, module
  `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology`;
- `lem-pbc-s2-dense-open-high-cohomology-high`, module
  `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh`;
- `lem-pbc-s2-dense-open-high-cohomology-pullback`, module
  `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyPullback`.

This removes those dependencies from this item's route; other callers can still need them.
The separate pulled-back degree-two comparison is particularly unnecessary here.
The old geometric dependencies (Noetherianity, finitely many components, closed-point
residue fields, zero-dimensional cohomology, finite direct image and Leray) are now grouped
under the new boundary calculation. They remain planned dependencies there, and are not
claimed globally pruned. The open–closed sequence and long exact Ext sequence remain used.
The larger pullback-cohomology ladder node is also no longer needed by this proof;
its proved Ext-exactness dependency supplies precisely the facts actually called.
Every other old proof dependency removed from the item is retained in the boundary
node: curve setting, constructibility, closed-point residue fields, derived Leray,
Noetherianity, finitely many components, zero-dimensional cohomology, finite direct image.
These are relocated dependencies, not globally pruned nodes.

## Where the brief, the DAG or earlier work was wrong

The original mathematical statement is unchanged and no statement is disputed.
The initial plan asked for a separate higher-degree comparison, but it is unnecessary:
finite outer groups in the long exact sequence prove finiteness directly in every degree.
The source library already proves both the open–closed short exact sequence and the
cohomology exactness facts, including the connecting maps; these were reused.

`tools/blueprint_refs.py ancestor lem-pbc-a3-dense-open-cohomology-finiteness` prints None:
created.item records a module name rather than a node id. The new node's blueprint ancestry
was recovered from the existing nodes' blueprint.from records and points to the imported
`lemma-weil-pbc-curve-dense-open-reduction`. Its via list records the intervening reductions.
No tool was edited or bypassed.

A direct import of the newly split `DenseOpenHighCohomologyHigh` was initially unavailable
in the local compiled library. The final proof does not use either that module or the
older full comparison. This was resolved mathematically without copying the missing module.

The new boundary node retains the existing zero-dimensional cohomology theorem as a tool:
it supplies the cohomology of the closed complement, exactly as in the original plan,
and does not replace the unit's dense-open localization step.

## New nodes

`lem-pbc-g2-dense-open-boundary-cohomology`, at
`dag/nodes/sec-proper-base-change/lem-pbc-g2-dense-open-boundary-cohomology.json`, records
`AlgebraicGeometry.IsCurve.dense_open_boundary_cohomology`, module
`Sheaf.AlgebraicGeometry.Curve.DenseOpenBoundaryCohomology`.
Its statement gives finite degree-zero and zero positive-degree cohomology for the
canonical closed-boundary sheaf. Its docstring and DAG contain the full geometric argument
and identify the existing geometric dependencies. LeanFinder and grep found no direct
replacement; LeanSearch returned Internal Server Error, recorded as unavailable rather
than as a negative mathematical result. No change record is needed: existing statements,
definitions, and public imports were not changed.

## Second reading by G2

1. Compared the complete item module by diff with the repository version. Its existing
   theorem signature and docstring are byte for byte unchanged. The additions are a private
   proved group helper, proof-only imports, and the proof body. The new boundary theorem is
   a separate geometric calculation, not the original equivalence under a new name.
   No existing definition or public import changed; no change record is required.
2. Compiled both modules together through lcompile.py without errors or warnings. A scratch
   copy with `#print axioms` showed only propext, Classical.choice and Quot.sound for the
   private helper, and those axioms plus sorryAx for the item and boundary theorem.
   The latter is the reported open geometric dependency. Read every proof step: the
   complementary-range equality gives the open–closed complex, Gabber's proved
   shortExact_map_forget₂ gives its abelian short exactness, H^0 injectivity transfers
   finiteness downward, and exactness plus finite outer groups handles both remaining
   directions in every degree. There are no forbidden declarations or hollow definitions.
3. Read Stacks Tag 0GJA, specifically its closed-boundary paragraph, against each hypothesis
   and conclusion of dense_open_boundary_cohomology. IsCurve supplies separatedness,
   finite type and dimension at most one. Noetherianity and density put all generic points
   in U and leave a finite zero-dimensional reduced complement; closed-point residue
   fields are k. Constructibility means finitely generated geometric stalk modules, hence
   finite over finite Λ. The zero-dimensional theorem computes their finite product;
   finite direct-image exactness and Leray give the asserted boundary cohomology.
   These arguments allow X empty, U=X, zero-dimensional components and the zero ring.
   The docstring gives the complete argument. Repeated LeanFinder and Mathlib grep through
   msearch with different queries, and searched the local curve, constructible-sheaf and
   finite-support modules. No direct replacement was found. The upstream finite-support
   vanishing theorem still needs the geometric hypotheses and does not give finite H^0;
   the existing zero-dimensional theorem is retained as a tool. Closing the geometric
   split is not a short application of either result.
4. Read dag/units/sk-thm-p1.json, including its realized fields. The dense-open localization
   and zero-dimensional boundary route remains; no unit statement or step was bypassed.
   Checked all old proof_deps: higher-cohomology comparison is pruned, geometric facts
   move to the boundary node, and the pullback ladder is replaced by its existing proved
   Ext-exactness node. Expanded No longer needed to account for every old dependency.
   Found that the boundary module did not import the modules of its open proof plan:
   added proof-only imports of ZeroDimensionalCohomology, CohomologyPullbackDerivedUnit,
   finite direct-image exactness, Noetherianity and closed-point residue fields so that
   those planned dependencies remain reachable by the import-based queue. The explicit
   public ideal-sheaf subscheme import supplies the data used in its statement; the closed
   immersion facts are now a plain proof import.
5. Read both delivered node files against the Lean, and opened the recorded dependency
   declarations. The new node has source, complete proof steps, matching signature,
   ancestry, unit, searches, status and creation fields. Corrected the item's two exactness
   steps and proof_deps to cite lem-weil-pbc-sheaf-ext-cohomology-long-exact, whose recorded
   declarations are exactly H.δSucc, H.exact_δSucc_map, H.exact_map_map and degree-zero
   injectivity used here. The larger pullback ladder itself is never applied. The existing
   forgetful-exactness node records the same general operation; the proof explicitly reuses
   Gabber's already proved constant-coefficient specialization rather than restating it.

Second reading changed only DAG exactness citations, the completeness of the pruning report,
and the new boundary module's proof-plan imports and import visibility. The main Lean proof
was correct and was retained. One original theorem is closed conditionally on one genuine
geometric split; the private algebraic helper is fully proved.
