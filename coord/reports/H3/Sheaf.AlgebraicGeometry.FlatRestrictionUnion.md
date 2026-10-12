## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isFlat_restrict_iSup_of_finiteLocallyFree` with its
original signature and visibility. Set W to the union, choose a covering member for each
point of W, and use the resulting Type u-indexed family of open immersions into W. The source
library's `isFiniteLocallyFree_of_isOpenImmersion` glues the restrictions to give finite local
freeness with varying rank on W. The already proved
`finiteLocallyFree_tensorLeft_exact` supplies finite-limit and finite-colimit preservation;
the braided tensor comparison transfers both to tensorRight, exactly `SheafOfModules.IsFlat`.

Added proof-only imports `WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent` and
`Sheaf.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact`. Updated the item's node's
proof, proof_deps and proof_origin to follow this argument. No definitions, existing statements,
public imports or other modules changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.isFlat_restrict_iSup_of_finiteLocallyFree`
(node `lem-pc-flat-restriction-union`). No sorry remains in the item and none was added.
This is a proof, not a decomposition: the two central library results used here are already
proved. The draft intermediate modules were deleted before delivery.

The file compiles without errors or warnings through lcompile.py. A separate #print axioms
check of the target reports only propext, Classical.choice and Quot.sound. The argument covers an
empty index type (W has no points and hence an empty cover), rank zero, different ranks on
different components, and an index universe v larger than u. No finite subcover is chosen.

## No longer needed

Removed proof-only imports:
- `Sheaf.AlgebraicGeometry.TensorPullback` (node `def-pc-module-pullback`): the proof uses the
  existing ordinary restriction/pullback comparison rather than the explicit tensor formula.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` (node
  `def-pc-finite-locally-free`): this defines finite locally free morphisms, not module sheaves.

No separately stated flatness-locality or finite-local-freeness-implies-flatness lemma is
needed. The original stalkwise tensor-exactness argument is supplied by the existing proved
`Sheaf.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact`, node `lem-sc-ext-tensor-exact`.
The three public statement imports remain needed. These are local pruning statements;
other targets may still reach the removed modules.

## Where the brief, the DAG or earlier work was wrong

The original DAG cites `def-pc-finite-locally-free` for finite locally free module sheaves,
but that node defines finite locally free morphisms. The correct variable-rank sheaf notion
is `def-sc-finite-locally-free-sheaf`, and the original Lean signature already uses the correct
fixed-rank sheaf class. No signature or statement meaning changed. The original node's
statement/stmt_deps were left unchanged because this delivery owns only proof fields.

Mathlib searches via leanfinder, loogle and grep found module-level flatness and localization
lemmas but no exact sheaf result. Searching the project DAG and source library then found
the already proved finite-locally-free tensor-exactness theorem and open-immersion locality.
`lem-sc-ext-tensor-exact` is a generic exactness tool from the Picard-duality unit; using it
does not bypass any statement or step realized by sk-thm-picard-perfect (its realized lists
are empty). The underlying source proves locality by refining to finite free charts.

## Second reading by H3

1. Unchanged interface: compared the entire delivered Lean module with the repository
   version using diff. Only two proof-only imports and the theorem body differ. The existing
   theorem signature, visibility, public imports, docstrings and all definitions are byte for
   byte unchanged. There are no other delivered Lean modules or change records. PASS.
2. Proof and trust: independently compiled the delivered module through lcompile.py without
   errors or warnings. Inspected the whole body: no sorry, axiom, unsafe, opaque,
   implemented_by, extern, hollow definition or witness from an unproved existence theorem.
   The choice of a covering index uses the proved membership equivalence for iSup, not an
   unproved theorem. The independent scratch #print axioms check reports only propext,
   Classical.choice and Quot.sound. The descent isomorphism composes pullback-to-restriction,
   restriction composition and homOfLE_ι in the correct directions; the final braided
   isomorphism transfers both preservation properties to tensorRight. PASS.
3. Split statements: none added and no sorry split off. Read the existing finite local
   freeness descent theorem in FiniteDescent and finiteLocallyFree_tensorLeft_exact in
   FiniteLocallyFreeTensorExact; both have proofs and apply to exactly these module sheaves.
   Checked the empty union (the point-indexed cover is empty), rank zero, varying ranks and
   an indexing universe larger than the scheme universe. No finite subcover or common rank
   is assumed. PASS.
4. Short route and pruning: independently searched lean/Sheaf, the upstream module sources,
   and Mathlib through msearch grep for tensorRight exactness, flatness of restrictions and
   finite-local-freeness locality. Mathlib's hits concern ModuleCat, not the required module
   sheaves; no shorter applicable result was found. The proved locality theorem plus the
   existing tensor-exactness result avoids all new lemmas. Both new imports are proof-only
   and used. The original proof_deps not used by this proof are def-pc-finite-locally-free
   and def-pc-module-pullback, precisely the FiberDegree and TensorPullback imports listed
   above. Read dag/units/sk-thm-picard-perfect.json: its realized statement and step lists
   are empty; this local tool proof changes no unit realization or required route. PASS.
5. DAG agreement: checked proof steps and their union against proof_deps, and checked the
   existing tensor-exactness and finite-local-freeness nodes against their declarations.
   The node describes the point-indexed cover, the restriction comparison and local
   trivialization descent, then tensor exactness and braided comparison. Found two metadata
   faults: lean.statement had literal Unicode escapes rather than the original signature,
   and the proof still cited def-pc-module-pullback although its explicit tensorPullback
   declaration is unused. Restored the entire original lean record and removed that node
   from the second step and proof_deps. PASS after repair. The pre-existing statement's
   reference to finite locally free morphisms remains the reported upstream DAG error;
   the unchanged Lean statement uses finite locally free sheaves.

Second reading changed only those node metadata fields and appended this review. The Lean
proof was sound and needed no edits. Holes closed: one; holes added: zero.
