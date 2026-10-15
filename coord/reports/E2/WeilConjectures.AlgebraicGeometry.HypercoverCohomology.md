## What changed

Proved `AlgebraicGeometry.hypercover_cohomology` in
`WeilConjectures.AlgebraicGeometry.HypercoverCohomology` with its original signature.
The abelian clause is obtained from the existing module clause for `ULift ℤ` by an
explicit equivalence argument. All helper constructions and lemmas are private and proved.

The proof establishes homotopy invariance for arbitrary abelian coefficients using
Mathlib's simplicial prism homotopy, dualization, and the alternating coface complex.
It constructs coefficient comparison isomorphisms on hypercover cochains and on derived
cohomology, proves refinement compatibility, and transports the natural cocone and its
pointwise unique factorization. Fullness lifts cocone legs and faithfulness proves uniqueness.
The arbitrary-ring clause applies `AlgebraicGeometry.hypercover_cohomology_module_part`.
All new imports are proof-only; both original public imports remain unchanged.

Updated the comparison node's proof, proof dependencies, proof origin, and Lean attachment
to describe the actual source-module proof. No other module or interface was adapted. The static checker requests a record for added
proof-context commands; `coord/changes/hypercover-cohomology-proof-context.md` records
unchanged public signatures and the effect on every downstream user. The coefficient
finite-colimit fact is installed through local bindings only inside proofs, not as a global instance.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.hypercover_cohomology`.
Added 0 holes and split off 0 obligations. The item module contains no `sorry`.
This is a proof from an existing planned dependency, not a new decomposition.

The proof still uses the existing named hole
`AlgebraicGeometry.hypercover_cohomology_module_part`, node
`thm-weil-pbc-hypercover-cohomology-module-part`, in
`Sheaf.Paper.HypercoverCohomologyModule`. The geometric injective-resolution and
finite-refinement comparison remains that node's task. Its proof-only dependencies
remain needed through that module; this delivery does not claim they have been proved.

## No longer needed

The abelian coefficient clause node
`thm-weil-pbc-hypercover-cohomology-abelian-part` and module
`Sheaf.Paper.HypercoverCohomologyAbelian` are no longer needed by this theorem's proof.
The separate abelian geometric comparison is replaced by transport of the existing
integer-module comparison. The wrapper `Sheaf.Paper.HypercoverCohomology` is not imported.
No original public import was removed. Removed redundant explicit proof imports of
`Mathlib.Algebra.Homology.Opposite` and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`;
their APIs are already exported by the remaining imports. No geometric dependency of the module clause
is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The comparison node's Lean attachment named the duplicate declaration in
`Sheaf.Paper.HypercoverCohomology`, while this item is the source-library declaration.
The attachment now names the source module. The node's former two-clause plan cannot
be used directly here: `HypercoverCohomologyAbelian` imports this source module and
proves its statement by projecting the original theorem. Importing it back would cycle.
No change to that other module is needed for the coefficient-equivalence route.

The argument works also in degree zero: all homotopy and coefficient comparisons are
proved uniformly in `q : ℕ`. It introduces no new hypothesis on the scheme or the ring.
The unit `sk-prop-h2` has no realized nodes, so no mandated unit step was bypassed.

## Second reading by E2

1. Compared the delivered module with the repository version. The public theorem
   signature and existing public imports are byte-for-byte unchanged; added commands
   are confined to the proof context and the change record documents them.
2. Compiled the module with `lcompile.py`; it succeeds with no errors, and the module
   contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
   The only remaining named hole used by the proof is the pre-existing
   `hypercover_cohomology_module_part` dependency.
3. Checked the updated node and searched the library for duplicate declarations. The
   theorem statement is unchanged, the node attachment now names the source module,
   and no new split-off statement was added.
4. Reviewed the proof from the target downward. It uses the existing module clause,
   explicit simplicial homotopy and coefficient-equivalence transport, and removes
   redundant proof-only imports. The old abelian-part node is no longer needed by this
   source theorem, while the module-part dependency remains required.
5. Checked the unit record and route. The unit `sk-prop-h2` has no realized nodes, so
   the proof does not bypass a mandated realized step; the theorem and its node retain
   the original statement and source route.

Changed only the report after this review; no proof or interface repair was necessary.
