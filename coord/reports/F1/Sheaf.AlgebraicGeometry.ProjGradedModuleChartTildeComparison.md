## What changed

Proved the existing declaration
`AlgebraicGeometry.Proj.gradedModuleChart_tildeComparison` without changing its signature,
visibility, public imports, or existing docstrings. Added the proof-only import
`Sheaf.AlgebraicGeometry.ProjGradedModuleChartBasisComparison` and replaced the proof-only
`Sheaf.Topology.SheafOfModulesFromBasis` import with Mathlib's
`Mathlib.Topology.Sheaves.SheafCondition.Sites`.

The proof obtains the localization comparisons from `gradedModuleAwayRestriction`.
It identifies the constructed submodules with Z by carrier equality, proves equality
of module restriction maps on arbitrary fraction representatives, and proves equality
of ring restrictions by the ordinary localization universal property and injectivity
of homogeneous localization. Those comparisons supply the hypotheses of the new
sectionwise lemma. The parent proves the pulled-back principal opens form a basis.
Its proved private helper `chart_iso_of_basis` extends the additive maps, checks
linearity locally using naturality and section extensionality, proves bijectivity on
basis components, and reflects the resulting additive-sheaf isomorphism back to
sheaves of modules. All Lean files compile cleanly using lcompile.py.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Proj.gradedModuleChart_tildeComparison`
(node `lem-weil-pbc-proj-graded-module-chart-tilde-comparison`). No sorry remains in the
item's module. The private helper `chart_iso_of_basis` is completely proved.

Added exactly one hole:
`AlgebraicGeometry.Proj.gradedModuleChart_basisComparison`
(node `lem-weil-pbc-proj-graded-module-chart-basis-comparison`), in its own new module
`Sheaf.AlgebraicGeometry.ProjGradedModuleChartBasisComparison`.
Its entire proof is `by sorry`; its docstring and node give the complete remaining
principal-open comparison argument. This is a decomposition, not a net hole reduction:
one original hole closed, one smaller hole added, net zero. The new statement does
not assume a grading of M or the fraction restriction laws; it assumes the localized
module and ring equivalences that the parent actually obtains and aligns in Lean.
It concludes only a compatible family of linear section equivalences on the fixed
principal basis, with no global sheaf morphism. Thus the alignment and sheaf-gluing
steps have been proved rather than moved under a new name.

Edge cases checked in the statement and the source argument: r=0 gives the empty
principal open; nilpotent f gives an empty chart and zero localized modules; M=0
and the zero ring cause no extra assumptions. Degrees need only be positive, not
one, and there is no finite-generation hypothesis. The basis proof and morphism
extension require neither nonempty bases nor finite coverings. No data definition
chooses a witness from an unproved mere-existence statement; both uses of the
existential comparisons occur only inside a theorem proof.

## No longer needed

Removed the proof-only import `Sheaf.Topology.SheafOfModulesFromBasis`, and removed
`lem-weil-pbc-sheaf-of-modules-from-basis` from the parent's proof dependencies.
The construction of a new module sheaf from finite basis gluing, intersection
closure, and finite refinements is unnecessary here: E and G are already sheaves.
Only the Mathlib morphism-extension and basis-isomorphism detection APIs are used.
The new helper uses only Mathlib public imports: the unnecessary copied
DegreeZeroFractions and Coherent imports were removed, and its module-sheaf types
use Mathlib Scheme.Modules and ringCatSheaf directly. The parent keeps its existing
public imports and signature exactly.
This is pruning from this item's route; it does not claim the module is absent from
other targets' import closures.

`lem-weil-pbc-spec-module-tilde-sections` moves from the parent's immediate proof
plan to the new node's proof dependencies, so it is not pruned. The graded away
restriction module and the affine-chart geometry remain needed. No unit statement
or unit proof step is removed; these nodes are below the realized unit layer.
No other imports, nodes, or modules are claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox held an unchanged holed parent and an empty new helper file;
there was no Lean reduction or node to preserve. This delivery supplies both.
The DAG's final step cited construction of an extension from a basis, although
morphism extension between existing sheaves suffices and has no finite-refinement
hypothesis. The new parent proof follows that shorter final step.

The local literature checkout is absent. Read the cited source directly at
https://stacks.math.columbia.edu/tag/01MB,
https://stacks.math.columbia.edu/tag/01M4, and
https://stacks.math.columbia.edu/tag/01M7. Searches in Mathlib and the project found
no exact chart-section comparison. LeanSearch returned Internal Server Error,
recorded as unavailable rather than a negative search result. LeanFinder, Loogle,
and grep results are recorded in the sandbox search log and the new node.

## New nodes

`lem-weil-pbc-proj-graded-module-chart-basis-comparison`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-proj-graded-module-chart-basis-comparison.json`,
realized by `Sheaf.AlgebraicGeometry.ProjGradedModuleChartBasisComparison` and
`AlgebraicGeometry.Proj.gradedModuleChart_basisComparison`. It retains the
principal-open geometry and section comparison portion of Stacks 01MB, assuming
the localization comparisons already established and aligned in the parent.
The new node carries its source, proof, searches, and Lean signature. The parent
node's proof, proof_deps, and proof_origin are updated to match the compiled proof.
No existing statement or definition changes, forced adaptations, or change records.

## Second reading by F1

1. **No accidental interface changes.** Compared both delivered modules with the repository versions. The existing parent theorem signature and all existing declarations are byte-for-byte unchanged; the only parent edits are proof-only imports, the private helper, and the proof. The new basis-comparison theorem is a separate declaration with its own node.

2. **Compilation and proof checks.** Compiled both modules with `lcompile.py --all`; they compile without errors or warnings. The parent theorem has no `sorry`; the sole remaining `sorry` is the named theorem `gradedModuleChart_basisComparison`, exactly as listed above. No forbidden declarations or hollow definitions occur. The parent proof uses only the permitted imported result and the explicit private helper; the helper is fully proved.

3. **Statement and node review.** Checked the new theorem against its Lean signature and node. It asserts only compatible sectionwise linear equivalences on the principal-open basis, with the localization comparison data supplied as hypotheses, and is strictly weaker than the parent target. Its docstring gives the source and a complete mathematical proof plan; the node records the same statement, source, proof steps, dependencies, and searches. Edge cases (zero and nilpotent principal elements, zero modules, and empty opens) do not add hypotheses or alter the conclusion.

4. **Pruning and route.** The parent proof follows the realized unit route through the chart intersection and graded-away-restriction nodes, then uses the new sectionwise comparison and Mathlib's basis extension. The former finite-refinement sheaf-construction import and dependency are unused and were removed; all remaining imports are used. No realized unit statement or step was bypassed.

5. **DAG consistency.** Verified the parent and new node `proof`, `proof_deps`, and `proof_origin` against the Lean proof and imports. The parent node records the split-off theorem and the new node records its declaration and module. No statement, definition, change record, or forced adaptation is needed.

Changed during second reading: appended this review only; no Lean or DAG repair was necessary.
