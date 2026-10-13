## What changed

Completed `AlgebraicGeometry.Etale.rawModuleScalar_source_square` from two genuine
parts, both now proved: the underived scalar composition equation and the generic
single-complex derived source square. The source attachment calculation is a
proved private helper. No existing library signature or target statement changes.

`RawModuleScalarSheafComposition` reuses the proved private unit calculations from
`RawModuleFreeSourceHomBijective`. Transpose the composition square through the
abelian pullback adjunction, use the module and abelian composition-unit equations,
move the two scalar comparisons across lowerStarComp by naturality, and apply the
scalar-unit equation successively for a and h.

`RawModuleScalarSourceSquareCore` reuses the proved private single-complex calculations
from `EtalePullbackSingleComp`. It proves derived composition and natural-isomorphism
compatibility by localization of degreewise identities, reflects them through D⁺ → D,
and proves the source square by naturality and cancellation of isomorphisms.
The canonical derived isomorphism and the three source factors are concrete definitions
in `RawModuleScalarDerivedPullbackIso` and `RawModuleScalarSourceFactors`.

The repository base lacks the dispatched module and node. This renewed explicit brief
asks to complete the retained sandbox anyway. The delivery therefore restores that
module and its recorded signature, with the four helper modules and their nodes.
It does not claim to close a hole on the current base or to change the measured target
closure. The independent reader can review this restoration explicitly. The change
record is `coord/changes/restore-raw-module-scalar-source-square.md`.

## Proved and sorry left

Closed the dispatched source-square hole:
`AlgebraicGeometry.Etale.rawModuleScalar_source_square`
(`lem-sbc-raw-scalar-source-square`).

Also closed both retained sandbox intermediate holes:
`CategoryTheory.Functor.plus_single_source_square_core`
(`lem-sbc-raw-scalar-source-square-core`) and
`AlgebraicGeometry.Etale.rawModuleScalar_sheaf_composition`
(`lem-sbc-raw-scalar-sheaf-composition`). All private helpers are proved.
No sorry remains in any delivered module; no holes were added or split off.
The second reader printed the axioms of all eight public declarations: each uses
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The dry-run axiom probes additionally check every delivered private declaration.
These are three retained sandbox holes closed, including the one dispatched item
hole; the current repository has none of these modules, so no current-baseline
hole closure or target-closure decrease is claimed.

## No longer needed

Removed from `RawModuleScalarSourceSquareCore` the imports of
`Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition` and
`Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`.
The generic proof needs only the derived exact-functor API. The second reader also
removed the redundant public import of
`Mathlib.CategoryTheory.Limits.Preserves.Finite` from that module, and the redundant
public import of `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`
from the main module; both are already supplied by the remaining public imports.
Removed the unused public import of
`Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso` from
`RawModuleScalarSourceFactors`.

Both concrete scalar modules are still needed by the main square, so these import
removals prune no module from the main theorem's closure. No original unit statement
or step is bypassed; `sk-lem-failure-field.realized` has empty statement/step lists.
The earlier tautological expanded statement remains discarded. Removed the circular
proof dependencies that incorrectly pointed each helper back to the source square.

## Where the brief, the DAG or earlier work was wrong

The earlier ABANDON stopped because the module was absent from the refreshed base;
it did not complete the proof work requested by the renewed brief. The retained
sandbox was useful, but its generic source-square and underived composition holes
were still open, despite several earlier report paragraphs saying otherwise.
Those two holes are now actually proved and compiled.

The inherited helper node records cited the upper source-square node as a proof
dependency, creating cycles. Their dependencies now follow the downward Lean proof.
The two records carrying concrete constructions were mislabeled as statement nodes;
they are now definition nodes, with complete descriptions and no postponed data.
Removed inherited review/landing fields: these new proposed nodes have not been reviewed.

The earlier search records incorrectly claimed negative LeanSearch results.
LeanSearch is unavailable (Internal Server Error); the records now say so without
a negative verdict. LeanFinder identifies the Mathlib exact-functor APIs; Loogle
cannot index the project extension; local rg finds the two proved private APIs reused
above. The raw canonical scalar comparison is essential: an arbitrary comparison
isomorphism need not satisfy the same unit normalization.

## New nodes

`lem-sbc-raw-scalar-source-square` restores the dispatched theorem and records its
proof from underived scalar composition and the generic derived square.

`lem-sbc-raw-scalar-sheaf-composition` states and proves the underived composition
square, with no arbitrary source map and no derived or single-complex factors.
It uses the canonical scalar comparison and the inverse-image composition equation.

`lem-sbc-raw-scalar-source-square-core` states and proves the generic derived passage
for any four exact additive functors between abelian categories. Its hypotheses
include the underived source equation; its conclusion is the corresponding degree-n
single-complex equation. It has no scalar or scheme assumptions.

`def-sbc-raw-scalar-derived-pullback-iso` constructs the derived scalar comparison
by composing the canonical derived comparison isomorphisms.

`def-sbc-raw-scalar-source-factors` constructs the three degree-zero source factors.
Every construction is explicit and has no sorry. No existence witness is chosen.

Change record: `coord/changes/restore-raw-module-scalar-source-square.md`.

## Second reading by N4

1. Interface preservation: compared each sandbox module with its repository path.
   All five paths, and all five proposed node IDs, are absent from the current base;
   there is no existing declaration signature to alter. Checked every displayed
   signature against its node and the restoration change record. The restored
   square retains arbitrary E, L and t, arbitrary commutative coefficients, and
   arbitrary scheme arrows satisfying the composition equation. No target or
   existing consumer is edited. Verdict: pass as an explicitly reported restoration,
   not a claimed improvement in the current sorry ledger.
2. Proof validity: compiled all five files locally in import order without warnings.
   Read the underived unit calculation, adjunction transpose, source attachment,
   degreewise single-complex calculations, localization, faithful inclusion, and
   cancellation argument. No delivered file has sorry, axiom, unsafe, opaque,
   implemented_by, extern or a skipped kernel check. Printed the axioms of all eight
   public declarations in a scratch probe: only propext, Classical.choice and
   Quot.sound occur. All data definitions explicitly compose canonical maps and
   isomorphisms; no arbitrary existence witness is selected. Verdict: pass.
3. Intermediate statements: both retained intermediate holes are now proved;
   no open statement is split off. The sheaf composition equation is a strictly
   underived part of the argument; the generic theorem transports an assumed
   square and cannot replace the actual scalar composition proof. Checked identity
   arrows, zero maps and zero objects: the naturality/unit equations and cancellation
   remain valid, and the generic proof works for every integer n. Searched with
   an independent LeanFinder query about scalar comparisons and adjunction units,
   Loogle's single/comp query, and local rg of both library roots and Mathlib's
   exact-functor and Kan-extension modules. No usable public theorem states either
   full intermediate equation. The existing reusable calculations in
   EtalePullbackSingleComp and RawModuleFreeSourceHomBijective are private.
   ScalarInverseImageCompositionCoherence and ScalarForgetPullbackComparison
   concern different scalar sheaves on the Zariski site. Verdict: pass.
4. Route and pruning: the proof uses the canonical inverse-image composition
   unit equations, then naturality at t, then the generic derived calculation.
   Proof-only helper modules have plain imports. Removed two additional redundant
   public imports, with successful compilation of the generic module afterwards.
   Remaining public imports supply the actual theorem/definition interfaces.
   No module leaves the main theorem's closure, and no unit step is bypassed:
   sk-lem-failure-field.realized has empty statement and step realization lists.
   The earlier discarded restatement and circular dependencies are already listed
   in No longer needed. Verdict: pass.
5. DAG agreement: checked sources, constructions, the two proof stages, dependency
   unions, origin records, created records, Lean declarations, and blueprint/unit
   records for all five new nodes. Every external dependency exists; the two helper
   proof dependencies point downward, not back to the main theorem. The core node
   describes the actual degreewise/localization/cancellation proof, and definition
   nodes record concrete constructions. Verdict: pass.

Second-reading changes: removed two redundant imports and clarified the import
pruning, explicit axiom results, and restoration/baseline accounting in this report.
No declaration signature, definition body, proof body, or DAG route was changed.
