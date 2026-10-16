## What changed

Repaired every duplicate reported by the landing tools. Removed the item's copies of
`pulled_matrix_entry`, `matrix_coefficient_pullback`, `finiteFreeEvaluationCoords`,
its apply/single/matrix lemmas, and `finrank_cokernel_of_matrix`. The item now imports
and uses the existing APIs:

- `Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank`: generalized the existing
  coordinate and cokernel-dimension API to independent coefficient and module universes.
  Exposed the coordinate definition, matrix lemma and cokernel-dimension lemma. The
  apply and single-vector lemmas stay private. Its existing public corank theorem is
  unchanged. The biproduct import is public because the exposed definition uses it.
- `Sheaf.Paper.IntegralMatrixFunctionsPullback`: exposed the existing
  `matrix_coefficient_pullback`, with its statement and proof unchanged. Its
  `pulled_matrix_entry` remains private in that original module.
- `Sheaf.Paper.IntegralRegularCoefficientPullback`: exposed the existing
  `conjugated_morphism_square` and `continuous_function_unit_naturality`, with their
  statements and proofs unchanged, for reuse in the transport proof.

Also completed the retained coefficient-transport obligation. The proof uses the
existing `Mod.regularExtensionIso`, the scalar-extension unit's naturality, and the
existing scalar and scheme chart comparisons. A proved helper performs the biproduct
transport for an abstract monoidal functor; another proves the coefficient identity
for an abstract resulting transport. This avoids kernel conversion through the large
concrete inverse-image construction, without changing any definition or increasing a
compile limit. The transport structure is used only inside the theorem proof.

The item's original `integralMatrix_pointwise_rank` signature and docstring are
unchanged. Its geometric-evaluation, universe-lift and rank-nullity argument is
retained, now using the existing coordinate and matrix-pullback APIs. All changed
modules were copied from current shared sources. No source file was written in the
shared repository. All three API modules were unclaimed; there are no forced
adaptations of another group's item.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integralMatrix_pointwise_rank`.
Also proved the previously proposed split-off theorem
`AlgebraicGeometry.ProEtale.CondensedRing.nonempty_integralMatrixCoefficientTransport`
(node `lem-weil-pbc-integral-matrix-coefficient-transport`) in this delivery.
All private helpers are proved. No new split-off obligation remains.

Actual delivered hole counts: the item has zero, the coefficient-transport module
has zero, and the three adapted API modules have zero. Relative to current main,
one original hole is closed and zero holes are added. The new module remains as a
proved intermediate API, rather than a decomposition awaiting another worker.

All five delivered modules compile through lcompile.py within the per-file limit.
The unchanged direct consumers `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`,
`Sheaf.Paper.IntegralMatrixAnalyticCover` and
`Sheaf.Paper.IntegralMatrixZeroNeighborhood` compile against the delivery overlay.
The transport theorem's axiom check contains only `propext`, `Classical.choice`, and
`Quot.sound`. The original pointwise-rank theorem still inherits `sorryAx` through
pre-existing geometric-evaluation dependencies; this is not an axiom-clean proof of
the whole import closure. No delivered declaration directly uses `sorry`.

## No longer needed

Removed the direct proof imports `Sheaf.Paper.GeometricFieldProEtaleEvaluation` and
`Sheaf.Paper.ContinuousCoefficientRealizations` from the main-branch item. Their
old direct proof-dependency nodes are removed from the item's `proof_deps`:
`lem-weil-pbc-geometric-field-proetale-evaluation` and
`lem-weil-pbc-continuous-coefficient-realizations`. Both remain reachable through
other required modules, so no globally prunable module is claimed.

Relative to the returned sandbox, removed the direct proof import
`Sheaf.Paper.IntegralRegularCoefficientPullback` from the item and replaced it with
`Sheaf.Paper.IntegralMatrixFunctionsPullback`; the former is still used in the
transport module. The original regular-coefficient node is replaced in the item's
`proof_deps` by the matrix-functions and corank API nodes. The iterated theorem
`integralMatrixFunctions_pullback` itself is unused; its module's existing coefficient
lemma is used directly. All seven copied helper declarations listed above are gone.

Removed the redundant direct `Mathlib.Algebra.Category.ModuleCat.Biproducts` proof
import from the item because the generalized coordinate API now exports it. The
previous reading had also removed redundant direct imports of
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`,
`Mathlib.Algebra.Category.ModuleCat.Kernels`, and
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`; these remain absent.
No entire module or unit step is claimed pruned from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated private helpers already present in other modules.
This repair generalizes or exposes those original APIs and imports them. The copied
helpers are removed, rather than renamed. The duplicate-statement check passes.

The earlier scalar-extension attempt rebuilt an existing regular-module comparison
and got stuck converting the concrete inverse-image construction in the coefficient
proof. `Mod.regularExtensionIso` already provides that comparison. Proving the
coefficient calculation with an abstract transport functor makes the full argument
check in the kernel. The previously reported lower hole is now closed here.

The original DAG suppressed the scalar-extension/continuous-coefficient comparison
and the field-universe mismatch. Both are now implemented. Node proof records follow
the actual reused APIs. No mathematical statement is disputed or weakened. Zero
source, target and cokernel ranks and empty schemes require no additional hypotheses.
All reused nodes belong to `sk-thm-properbasechange`; its realized statement and
three unit steps are preserved.

## New nodes

`lem-weil-pbc-integral-matrix-coefficient-transport` is retained from the proposed
delivery, now with a complete proof and corrected proof dependencies. It records the
scalar-extension/inverse-image transport, the coefficient equation, and preservation
of a supplied free-cokernel trivialization. It asserts no rank or cover constancy.
No further node or holed theorem is introduced in this repair.

Change records:
`coord/changes/integral-matrix-pointwise-rank-helper-commands.md`,
`coord/changes/E4-reuse-CondensedFieldPresentationCorank.md`,
`coord/changes/E4-reuse-IntegralMatrixFunctionsPullback.md`, and
`coord/changes/E4-reuse-IntegralRegularCoefficientPullback.md`.
Each lists the affected API, old and new commands, and its users. No target-used
definition changes meaning, so no target statement review is reopened.

## Second reading by E4

1. Compared all four existing delivered modules with the shared sources and read
   the new transport module in full. The original pointwise-rank signature is
   byte-for-byte identical. The only existing interface changes are the declared
   exposure of private helpers, the independent field/module universe parameters
   in the coordinate/cokernel API, and its public biproduct import. The old
   universe specialization and coordinate construction are preserved. The public
   corank theorem and both existing pullback theorems are unchanged. The change
   records describe these edits; all three API modules are currently unclaimed.
   Verdict: no accidental statement or definition change.

2. Independently compiled all five delivered modules through lcompile.py: no
   errors or warnings, each within 10 seconds. Searched all delivered Lean files
   for holes and forbidden declarations/options: none. Explicit scratch
   `#print axioms` checks of the transport theorem and all six exposed coordinate,
   dimension and coefficient declarations show only propext, Classical.choice
   and Quot.sound. The original rank theorem additionally inherits sorryAx from
   its existing geometric-evaluation dependencies, as already disclosed above.
   The scalar-transport functor and regular comparisons are actual constructions;
   no definition chooses arbitrary data from an unproved existence theorem.
   Independently compiled unchanged direct consumers
   CondensedFieldLfpLocalTriviality, IntegralLfpLocalTorsionCharts,
   IntegralMatrixAnalyticCover and IntegralMatrixZeroNeighborhood against the
   delivery overlay; all passed without warnings. Verdict: the local proof is
   complete, with the stated pre-existing dependency limitation.

3. No split-off hole remains. Read the proved transport theorem, its structure,
   docstring proof and node together. It supplies scalar/scheme transport and a
   coefficient equation, without asserting rank constancy or geometric
   evaluation, so it is a strictly smaller part of the argument. Checked zero
   source/target ranks, q=0 and empty schemes: biproduct transport and cokernel
   dimension still apply, and coefficients are asserted only at actual points.
   Independent LeanFinder search for additive finite-free presentations and
   Loogle search `Matrix.rank, Module.finrank` found generic matrix/range facts,
   not this combined transport theorem. Local searches found the regular
   extension API already reused here and confirmed removal of the duplicate
   coordinate and pullback helpers from the item. Verdict: no new unproved or
   duplicate obligation.

4. Followed the proof from rank constancy down to the common free-cokernel rank,
   its evaluation dimension, the matrix-coordinate identity and coefficient
   transport. The bound rank <= t is used when cancelling natural subtraction;
   no extra hypothesis is introduced. The imported generic coordinate and
   rank-nullity lemmas provide the direct linear-algebra route. Proof imports
   are private; public imports support statements or the exposed definition.
   The two original proof-dependency nodes removed from the item are both
   explicitly listed under No longer needed. Neither disappears from the import
   closure, so no whole-module pruning is claimed. Checked
   dag/units/sk-thm-properbasechange.json: its realized statement and all three
   steps are preserved. Verdict: reduction and pruning respect the unit route.

5. Compared both node proof plans with the actual Lean argument. Each
   proof_deps list is exactly the union of its steps' uses; proof_origin records
   the scalar transport, universe lift and reused APIs. The new node has source,
   statement dependencies, searches, creation/blueprint metadata, chapter/unit
   and a matching Lean record. The original node's statement is unchanged.
   Verdict: records agree with the proof.

Second-reading changes: appended this review and its independent verification
results only. No Lean code, node or change-record repair was needed. The delivery
closes one original hole, adds zero holes, and leaves zero split-off obligations.
