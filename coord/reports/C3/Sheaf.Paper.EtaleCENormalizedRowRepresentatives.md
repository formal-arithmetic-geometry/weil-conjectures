## What changed

Replaced `AlgebraicGeometry.Etale.exists_etaleCE_normalized_row_representatives` with a complete Lean proof, preserving its signature and both public imports. The proof uses two strictly smaller remaining statements: normalized presentation construction and degreewise naturality on row cycles. It constructs the requested family `e` as the concrete signed row comparison and proves the homology representative equation by `HomologicalComplex.homologyπ_naturality`, the canonical projection formulas, and scalar compatibility.

The new `Sheaf.Paper.EtaleCECanonicalRowComparison` module is fully proved. It specializes the already proved `secondFiltration_row_cycle_comparison`, retains all three normalizing equations, proves the cycle-class map invertible using `secondFiltration_row_graded_cycles`, and constructs `rowCyclesIso` and `signedRowComparison`. Its projection formula follows by inverse-isomorphism cancellation. No data is chosen from an unproved theorem in these definitions: the underlying existence and graded-cycle comparison theorems are proved, and the normalizations determine the maps used downstream.

`Sheaf.Paper.EtaleCENormalizedRowPresentations` and `Sheaf.Paper.EtaleCERowCyclesNaturality` each state one public theorem with its complete source proof in words. The former contains no scheme-map naturality assertion. The latter is an equality on cycles before homology for arbitrary presentations, with no coefficient-map augmentation hypothesis or normalized higher-page construction. Thus neither restates the original theorem.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.Etale.exists_etaleCE_normalized_row_representatives` (node `lem-weil-pbc-ce-normalized-row-representatives`). Added two holes:

- `AlgebraicGeometry.Etale.exists_etaleCE_normalized_row_presentations`, node `lem-weil-pbc-ce-normalized-row-presentations`.
- `AlgebraicGeometry.Etale.etaleCE_row_cycles_naturality`, node `lem-weil-pbc-ce-row-cycles-naturality`.

This is a decomposition: one original hole closed and two smaller holes added, net minus one hole. The canonical row-comparison module has no `sorry`. All four delivered modules compile. The delivery dry run checks their axioms and remaining named holes.

The edge cases for the new statements were checked against the construction: negative q uses the interval [q,q+p], p=0 uses the same cycle kernel with zero incoming boundaries, and zero rows and empty schemes use the same zero-object and cokernel universal properties. No cancellation of a non-epic row map is assumed.

## No longer needed

Removed the unnecessary `FilteredComplexNormalizedHomology` import from the newly drafted row-cycle module. No existing-library import is removed. Both public imports of the target are needed by its signature. The old immediate proof dependencies are no longer immediate: `thm-sp-if-e1`, `lem-sp-cartan-eilenberg-row-pages`, `lem-sp-filtered-complex-page-differential`, `lem-sp-filtered-complex-normalized-homology`, `lem-sp-filtered-complex-graded-homology`, `lem-weil-pbc-ce-row-ordinary-naturality`, and `lem-weil-pbc-ce-total-sections-comparison`. They remain dependencies of the new subproblems. No original planned node is globally pruned: the presentation subproblem retains `thm-sp-if-e1`, `lem-sp-cartan-eilenberg-row-pages`, the filtered page, graded homology and normalized homology nodes, and ordinary row naturality; the cycle subproblem retains the total-sections comparison and canonical row-cycle tools. The target's immediate proof dependencies are now the two subproblems and the canonical row-comparison package. No proof uses an upstream theorem that depends on this target, and no unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The original named dependencies give objectwise row-page and abutment comparisons, but their public signatures do not provide the simultaneously normalized presentation construction or the representative naturality equality. Those two portions of the plan are now explicit statements. In particular, an arbitrary objectwise row-homology isomorphism would not suffice for naturality: this delivery fixes it by its diagonal-cycle and quotient equations.

The target retains unused coefficient/augmentation hypotheses because its existing signature is fixed; the cycle equality only needs the diagonal-compatible total map. A declaration-local unused-variable linter option avoids changing those binders.

## New nodes

`def-weil-pbc-ce-canonical-row-comparison` records the concrete definitions, their normalizing equations, invertibility and projection formula in `Sheaf.Paper.EtaleCECanonicalRowComparison`. It uses the proved row-cycle and graded-cycle nodes.

`lem-weil-pbc-ce-normalized-row-presentations` records the construction of simultaneous normalized presentations and the prescribed signed first-page identity in `Sheaf.Paper.EtaleCENormalizedRowPresentations`. It covers steps 1–2 of the original plan, without the representative equation.

`lem-weil-pbc-ce-row-cycles-naturality` records the degreewise row-cycle representative equation in `Sheaf.Paper.EtaleCERowCyclesNaturality`. It isolates the finite-diagonal projection calculation of step 3; the passage to homology and the sign calculation are proved in the target module.

No existing definition, statement or visibility changed, and no forced adaptation or change record is needed.


## Second reading by C3

1. **Unchanged interface — pass.** Compared the sole existing delivered module with
   the repository using diff, then compared the complete theorem signature byte for
   byte. Restored one extra space immediately before `:=`; the signatures now match
   exactly. Both existing public imports and the existing docstring are retained.
   The other three modules are new; no definition or existing statement changes.
2. **Kernel proof and data — pass as a decomposition.** Independently compiled all
   four modules through lcompile.py, without errors or warnings. Scanned every
   delivered Lean file: the only two sorries are the public named split theorems;
   no forbidden declarations or hollow definitions occur. Scratch-copy `#print axioms`
   checks of all ten canonical comparison declarations show only propext,
   Classical.choice and Quot.sound. The target shows those plus sorryAx, expected
   from its two subproblems. The definitions choose witnesses of a proved theorem,
   and the diagonal, cycle and quotient normalizations determine them uniquely by
   monicity and epic quotient cancellation. No arbitrary witness of an unproved
   existence statement is used as definition data.
3. **Split statements — pass.** Read both complete signatures and their docstring
   proofs. The presentation theorem isolates simultaneous normalized construction
   and the pinned first-page comparison; it contains no representative naturality.
   Cycle naturality isolates the finite-diagonal calculation, applies to arbitrary
   presentations, and contains neither the presentation existence claim nor the
   homology equation. Both are true strict parts of the original argument. Checked
   p=0, negative q (interval [q,q+p]), zero rows and empty schemes: projection and
   kernel/cokernel arguments remain valid and require no nonzero hypothesis.
   Fresh msearch leanfinder query "Associated graded of total complex second
   filtration canonical row cycles projection naturality" returned total-complex
   inclusion/map and cycle-inclusion component lemmas, not either split statement.
   Fresh loogle query `"cyclesMap", "iCycles"` and grep query
   `secondFiltration.*[Nn]atural|[Nn]ormalized.*[Ss]uccessor|row[Cc]ycles.*[Mm]ap`
   returned no matches. Independently searched lean/Sheaf and lean/WeilConjectures
   for row projection/naturality and normalized presentations, and read the proved
   row-cycle, graded-cycle, signed-first-page and hypercohomology-first-page modules.
   No already-stated replacement or quick closure of either subproblem was found.
4. **Route and pruning — pass.** Read the top proof downward: the first split supplies
   P, delta and j; e is constructed, the second split supplies a cycle equation,
   and the actual passage to homology and signed-scalar calculation is proved here
   using homologyπ_naturality. The canonical package reuses the already proved
   library comparisons. Every public import of the new modules supplies symbols
   used in their statements or definition bodies; the graded-cycle proof import
   and target's new proof imports are private. Read dag/units/sk-prop-h2.json:
   its realized lists are empty and its Kummer/Picard/Brauer route is untouched.
   All seven old immediate proof dependencies remain below the new subproblems;
   expanded No longer needed to enumerate them explicitly. No module is pruned.
5. **DAG correspondence — pass after repair.** Read all four delivered node records,
   compared their statements with Lean, and checked proof dependency unions and
   origins. New records contain source, search, created, blueprint, chapter, unit
   and Lean data. Replaced flattened lean.statement values with verbatim signatures
   (using the delivery parser’s declaration boundaries). Marked the canonical construction
   and final target calculation non-elementary: both use named node results.
   The proof plans and dependency sets otherwise agree with the implementation.

Second-reading changes: exact signature whitespace, verbatim DAG signatures,
non-elementary flags for steps using node results, explicit old-dependency pruning
inventory, and this independent review. No mathematical proof rewrite was needed.
The result remains a decomposition: one original hole closed, two added, net -1.
