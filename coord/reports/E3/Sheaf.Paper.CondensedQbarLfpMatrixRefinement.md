## What changed

Proved `AlgebraicGeometry.ProEtale.exists_condensedQbar_finiteFree_refinement` in
`lean/Sheaf/Paper/CondensedQbarLfpMatrixRefinement.lean`, with its signature and visibility
unchanged, from one strictly smaller compatible-presentation theorem. The original four
public imports are unchanged; all additional imports in this module are proof-only.

The parent now proves coefficient normalization, the comparison of condensed Qbar coefficients
with the sheafification of bounded continuous functions, rank descent and local constancy,
bounded Gaussian elimination, the categorical cokernel calculation, and cover assembly. The
coefficient comparison includes explicit universe transport of the existing finite-field
comparison through ULift, its adjoint normalization equation, naturality in finite subfields,
and passage to filtered colimits. Multiplicativity is proved using tensor products of these
colimit cocones. No covering scheme or open subscheme is assumed noetherian.

Added `lean/Sheaf/Paper/CondensedQbarFunctionPresentations.lean`. Its two definitions
`AlgebraicGeometry.ProEtale.condensedQbarFunctionEval` and
`AlgebraicGeometry.ProEtale.condensedQbarFunctionComp` are explicit evaluation and restriction
ring homomorphisms. Its remaining theorem receives the already proved coefficient-ring
isomorphism and supplies compatible function matrices and presentations on open restrictions.
It asserts neither local constancy nor local freeness. Updated the original node's proof route
and added the node for this remaining theorem. No other existing module is changed.

## Proved and sorry left

Closed the original single hole in
`AlgebraicGeometry.ProEtale.exists_condensedQbar_finiteFree_refinement`
(node `lem-weil-pbc-condensed-qbar-lfp-matrix-refinement`). There is no sorry in the item module.

Added one hole, exactly the public theorem
`AlgebraicGeometry.ProEtale.exists_condensedQbar_compatible_function_presentations`
(node `lem-weil-pbc-condensed-qbar-compatible-function-presentations`), in its own module.
Its proof is exactly `by sorry`. This is a decomposition: one hole closed and one added,
net zero holes, not a claim of net proof progress. The substantial completed work is the
coefficient comparison and all subsequent rank, matrix, cokernel, and covering arguments.

The remaining theorem still needs the finite-presentation matrix on a weakly contractible
affine refinement, its natural realization by bounded functions, the ring homomorphisms
on open restrictions, and the comparison of the evaluated linear cokernels at two points
over the same point of X. The geometric evaluation must be lifted to the internal
`CategoryTheory.Mod` API used here. One route is to lift the already proved exact
Ab-valued evaluation functor through `mapMod` and then identify internal modules in Ab
with ordinary modules; alternatively transport the `SheafOfModules` evaluation API.
It does not need to prove the coefficient-ring comparison, quotient-dimension arithmetic, local constancy,
Gaussian elimination, or finite freeness; these are proved by the parent.

The main proof constructs actual module-sheaf isomorphisms from cokernels of biproduct maps.
It does not infer isomorphisms from fibre dimensions. Rank zero, empty row or column index
sets, and the empty scheme are included in the same proof. The quotient-dimension argument
uses finrank of the quotient and range, without truncated-subtraction cancellation.

Both delivery modules compile cleanly with the prescribed compiler. The ten checked private
helpers, including the entire coefficient comparison and all main proof components, depend
only on `propext`, `Classical.choice`, and `Quot.sound`. The parent theorem has the expected
`sorryAx` dependency from the one remaining presentation theorem. The final local compilation
of the two-module set took 11.5 seconds for the new module and 19.5 seconds for the parent; no time or heartbeat limit was raised.

## No longer needed

No existing public import was removed, and no existing node or module is globally pruned.
The original coefficient, basis, geometric-evaluation and cover dependencies remain needed
in the new presentation node or the proved parent. The local-freeness clause of
`Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` is not applied; only its proved,
canonically normalized coefficient-comparison theorem is used. The matrix ranks are computed
over Qbar throughout, so the planned separate change-of-field rank computation is unnecessary.

Removed the following original direct proof imports from the item:
`Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`,
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`Sheaf.CategoryTheory.SitePullbackAbelianExact`,
`Sheaf.NumberTheory.Padics.FiniteCoefficientFields`,
`Sheaf.Paper.CondensedPointBasisEvaluation`,
`Sheaf.Paper.GeometricFieldProEtaleEvaluation`, and
`Sheaf.Paper.ProfinitePointPullback`.
Their planned presentation/evaluation uses are recorded in the remaining node; the completed
parent proof imports the coefficient and matrix APIs it actually uses. Removing these direct
imports is not a claim that their modules are globally unreachable.

During additional import cleanup removed direct proof imports of
`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`,
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`, `Mathlib.Topology.NoetherianSpace`,
`Mathlib.Topology.Sober`, `Mathlib.Topology.LocallyConstant.Basic`, and
`Mathlib.CategoryTheory.Filtered.Final`; the needed declarations are provided transitively
by the imports that the proof uses. The old `Adic.UnitMatrix`, `Adic.Abelian`, and
`Adic.LisseAbelian` modules were examined but are not imported. Their lower-level proved
matrix lemmas suffice for the elimination argument; this is not a claim that these modules
are unused elsewhere in the project.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The proof plan is valid, but some of its
interfaces need explicit transport: the finite-field coefficient-comparison theorem places
its field in the scheme universe, and the existing module-valued geometric-evaluation
API uses `SheafOfModules` rather than internal module objects. The first transport, including
its normalization and naturality, is proved here. Lifting the underlying exact Ab-valued
evaluation to internal modules, or transporting the module-valued API, remains in the
presentation item.
The older Adic modules also introduce finite-coefficient notation that conflicts with the
module-object notation in this item; the proof uses their lower-level matrix lemmas instead.

An early concrete cover-composition proof exceeded the compiler limit because reducing a
composite cover unfolded the large extension-of-scalars definition of module pullback.
The final helper `cover_of_open_local_property` proves cover assembly for an arbitrary
property of a morphism, so no such concrete definition is unfolded. No shared definition or
compiler limit was changed, and the item was not split to evade the time limit.

The second dry run repeatedly re-entered `delivery_cache._load` because
`origin/sheaf-dag` advanced while its shared index was being built; the interrupted stack
showed ten nested reloads and a wait on `library-builder.lock`. The final required dry run
uses the tool's built-in `WEIL_DELIVERY_CACHE_DISABLE=1` mode. This selects the original
full source scanners, including the import-cycle and declaration checks; it disables no
validation, changes no tool, and raises no compiler limit.

The cited RefactorInstruction.tex checkout is absent on this machine. The source place and
full numbered argument in the existing node, the unit route, the recorded dependency
statements, and the proved source-library matrix and coefficient-comparison code were read.
The blueprint ancestor command did not follow the module-name entry in the item's creation
record; the new node records the established Qbar proper-base-change blueprint ancestor
and its explicit chain through the local-triviality and two-colimit nodes.

## New nodes

`lem-weil-pbc-condensed-qbar-compatible-function-presentations`, in
`dag/nodes/sec-proper-base-change/`, carries the one remaining theorem and the two concrete
function ring homomorphisms. Its hypothesis includes the coefficient-ring isomorphism
proved in the parent, and its conclusions stop at compatible linear cokernels and open
presentation maps. Thus it is strictly the initial matrix/evaluation portion of the argument,
not the original local-freeness assertion under another name. The node and docstring give
its source and the complete remaining argument; the recorded searches were actually run,
with the unavailable search service recorded without a no-match claim. No mathematical statement change
or forced adaptation of another module is needed. The static preflight does require a
record for the command scopes added around private helpers:
`coord/changes/condensed-qbar-matrix-proof-scopes.md`. It records the identical old/new
signature and the downstream-use check; no public mathematical interface changes.

## Second reading by E3

1. **Statements and interfaces.** I compared the delivered item module against the
repository version. The declaration of
`AlgebraicGeometry.ProEtale.exists_condensedQbar_finiteFree_refinement` is byte-for-byte
unchanged, including its hypotheses, conclusion, universe, and visibility. The two
explicit function homomorphisms and the split presentation theorem are new declarations
whose statements match the new DAG node. I found no altered definition or target
statement and no statement requiring `STATEMENT-DISPUTED`.

2. **Proof and axioms.** Both delivered modules compile independently and together with
`python3 /home/ubuntu/weil-launcher/lcompile.py --all`. The item contains no `sorry`,
`axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the only remaining `sorry`
is the named theorem
`AlgebraicGeometry.ProEtale.exists_condensedQbar_compatible_function_presentations`,
whose docstring gives the source and complete proof plan. The parent consequently has
the expected `sorryAx` only through that theorem; private completed helpers use only the
permitted axioms.

3. **New statement and node.** The split theorem is strictly weaker than the parent:
it supplies bounded function matrices, compatible evaluated cokernels, and open
presentation maps, while asserting no rank constancy, local freeness, or finite-free
conclusion. Its edge cases (empty matrices, zero rank, and empty covers) are included by
the quantified statement. The matching node records its source, proof route,
dependencies, Lean declaration, and recorded Mathlib searches; no duplicate declaration
was found in the library.

4. **Route and pruning.** The parent follows the unit route through coefficient
comparison, function presentations, fibrewise quotient-rank comparison, local constancy,
Schur elimination, categorical cokernels, and cover assembly. The DAG proof and
`proof_deps` were updated to include the split theorem and the declarations actually used.
No old proof dependency was silently removed from the node; direct imports removed from
the old implementation are documented under `## No longer needed`, with their planned
presentation/evaluation work isolated in the split node. The unit's `realized` route is
unchanged.

5. **Repair and changes made during this reading.** No Lean proof repair was necessary:
the two modules already compiled cleanly. I added this required second-reading record to
the report after the first dry run identified that the section was missing. The change
record for private command scopes remains present, and no source module, node statement,
or public interface was changed during the second reading.
