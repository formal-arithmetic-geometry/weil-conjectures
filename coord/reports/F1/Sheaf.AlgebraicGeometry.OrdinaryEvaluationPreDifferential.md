## What changed

Completed the earlier attempt's reduction of `AlgebraicGeometry.ordinaryEvaluation_pre_differential`, keeping its signature unchanged. Added proof-only imports of `Sheaf.AlgebraicGeometry.OrdinaryDualProjectionDifferential` and `Sheaf.AlgebraicGeometry.OrdinaryEvaluationPrecompositionNaturality`. The main proof splits on the support condition, applies the projected differential and evaluation naturality, and combines the signs using `Int.negOnePow_add`; outside the support both components are zero.

Proved `AlgebraicGeometry.ordinaryEvaluation_dual_projection_differential` from the differential clause of `CategoryTheory.homComplex_projections_exists`: the single complex has zero differential and internal Hom sends postcomposition by zero to zero. Added a proved private helper for this last fact. Scoped the transparency option needed by the main proof to its theorem. The two new modules publicly import only `Sheaf.AlgebraicGeometry.OrdinaryEvaluationData`, which supplies their signatures and proof ingredients; they do not need the bounded assembly theorem.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ordinaryEvaluation_pre_differential` (node `lem-pc-ordinary-evaluation-pre-differential`). No sorry remains in the item's module. Added and proved `AlgebraicGeometry.ordinaryEvaluation_dual_projection_differential` (node `lem-pc-ordinary-dual-projection-differential`).

One hole is split off: `AlgebraicGeometry.ordinaryEvaluation_precomposition_naturality`, node `lem-pc-ordinary-evaluation-precomposition-naturality`, in its own module. It is a strict part of the calculation: it concerns arbitrary maps and scalars satisfying a projection identity, and neither asserts a differential formula nor combines the tensor signs. This delivery is a decomposition of one original hole into one smaller hole, not a claim of a net reduction in holes. Existing imported prerequisite holes remain unchanged.

## No longer needed

No import was removed from the existing item. In each new module, replaced `public import Sheaf.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly` with the smaller `public import Sheaf.AlgebraicGeometry.OrdinaryEvaluationData`. The original parent node's direct proof dependencies `lem-pc-bounded-ordinary-evaluation-assembly`, `lem-pc-sheaf-modules-tensor-closed`, and `lem-sc-hom-complex-projections` are replaced by the two calculation nodes and `def-pc-ordinary-evaluation-data`. These original modules remain needed for statement reexports or underneath the calculation, so no globally pruned module is claimed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt contained two new statement modules without node records or a report. Added those records and proved the differential statement. The inherited main proof compiled; compilation and the required dry run were repeated after the repairs. No existing statement, definition, or unit route is changed.

## New nodes

`lem-pc-ordinary-dual-projection-differential`: the dual Hom differential projected onto the degree-zero structure sheaf. Its proof uses the recorded Hom projection formula and the zero differential of the single complex. Module `Sheaf.AlgebraicGeometry.OrdinaryDualProjectionDifferential`; proved.

`lem-pc-ordinary-evaluation-precomposition-naturality`: evaluation naturality under arbitrary precomposition maps and a scalar projection identity. Its docstring records the tensor-Hom naturality, scalar, and degree-transport argument. Module `Sheaf.AlgebraicGeometry.OrdinaryEvaluationPrecompositionNaturality`; the single remaining new sorry. Zero modules, arbitrary complexes, and all integer indices satisfying the specified equations meet the same argument; no boundedness or invertibility is asserted.

## Second reading by F1

1. Compared the item's full diff with the repository and checked the theorem signature by a
   byte-for-byte comparison: unchanged. Its existing local instance and definitions are unchanged.
   The only extra existing-file material is proof code, private sign helper, scoped elaboration
   option, and two plain proof imports. The other two modules are new. No change record is needed.
2. Compiled all three delivered modules with `lcompile.py --all`, without errors or warnings.
   Printed axioms in scratch copies: the dual projection theorem uses only `propext`,
   `Classical.choice`, and `Quot.sound`; the main theorem and naturality statement additionally
   use `sorryAx`, as reported. The sole delivered `sorry` is the named public naturality theorem.
   No forbidden declaration or attribute, hollow definition, or new choice of data is present.
   The original projection construction and proof-only choice of a preadditive instance are
   unchanged. Verdict: valid decomposition, one original hole closed and one smaller hole added.
3. Read both new statements against `localEvaluationComponent`, the Hom projection formula,
   and tensor-Hom naturality in all three arguments. The differential theorem is kernel-checked.
   For naturality, the supported component is evaluation of the assumed projection identity;
   transport composition is `XIsoOfEq_hom_comp_XIsoOfEq_hom`. Zero maps/modules, empty opens,
   equal input degrees, and both integer-unit signs impose no extra hypotheses. The statement
   handles arbitrary maps and does not assert a differential identity or combine the tensor
   signs, so it is a strict part of the parent argument. The docstring gives this complete
   calculation and the node records it. Repeated searches with different wording via leanfinder,
   loogle, and Mathlib grep, and searched the repository and upstream sheaf modules. Found the
   public tensor-Hom naturality lemmas and an existing *private* module-evaluation naturality
   proof, but no accessible theorem stating this projected calculation. An attempted proof using
   those ingredients in scratch copies did not finish within the single-file limit; it is not
   delivered. Checked the cited [ordinary evaluation source](https://stacks.math.columbia.edu/tag/08DQ),
   [Hom differential formula](https://stacks.math.columbia.edu/tag/0A8X), and
   [tensor-Hom adjunction](https://stacks.math.columbia.edu/tag/03EO). Verdict: true and needed.
4. The main proof calculates from the top: support split, proved projection differential,
   smaller evaluation naturality, and proved sign identity; the unsupported branch is zero.
   Its direct dependencies no longer include any of the three old proof dependencies, all
   listed in `No longer needed`. Their declarations remain in the import closure through data
   or retained public reexports, so no global pruning or net hole reduction is claimed.
   Reduced the new imports to the data module. Read `dag/units/sk-thm-picard-duality.json`:
   its statement, step, and `realized` fields are unchanged; this calculation is below the unit
   level and bypasses no realized unit node. Verdict: route preserved.
5. Checked every node's proof-dependency union and verbatim Lean signature. The parent changes
   only `proof`, `proof_deps`, and `proof_origin`; both new nodes carry the required creation,
   source, blueprint, chapter, unit, search, and Lean fields. Found and repaired the dual node's
   Lean record: it had pointed to private `projectionHomMap_zero` instead of public
   `ordinaryEvaluation_dual_projection_differential`. Corrected that node's source filename to
   `sites-cohomology.tex` for Tag 0A8X, and removed verdicts on unavailable leansearch entries.
   Verdict: nodes now agree with the delivered Lean.

Second reading changed the dual node's declaration/signature record and source, the two new
modules' imports, unavailable-search metadata, and this report. It changed no existing statement,
definition, or working proof.
