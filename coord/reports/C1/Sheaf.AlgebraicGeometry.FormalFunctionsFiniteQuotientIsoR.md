## What changed

Proved `AlgebraicGeometry.formalFunctions_finite_quotient_iso_r` by composing
ModuleCat morphisms as linear maps. The quotient-system isomorphism and its
component equation are already supplied by the hypotheses. No signature changed.
Replaced the public import of `Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoB`
with its three public statement dependencies, and updated the node's proof route.


Repair of return F (reviewer X-f065c): supplied the full unchanged direct-importer
source in the change record's Users section, so it is included in the review
packet even when the reviewer's clone is stale. Verified its original delivery
base `0598a8317d043664afba0354238cbda1cc9b02fc`, blob
`30ca1dedc8e7e09b3d260e580f1ba78f0b5ab3ad`, and byte identity at returned delivery
`f065cdcf09d9affa88f2ba981dcef95fe01d69fb`. Compiled that unchanged importer
against a freshly compiled copy of the delivered R module, in the same scratch
sandbox and import order, with lcompile.py. Both compiled with exit code zero
and no errors or warnings; the change record contains the output and reproduction
instructions. This repair changes only review evidence in this report and the
change record. No Lean proof, signature, node, or downstream source changed.

## Proved and sorry left

Closed the one hole: `AlgebraicGeometry.formalFunctions_finite_quotient_iso_r`
(node `lem-weil-pbc-formal-functions-finite-quotient-iso-r`). No holes remain in
this module and no new holes or nodes were added. This is a proof, not a decomposition.
Imported definitions may still depend on existing unfinished theory.

## No longer needed

Removed direct import `Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoB`;
its theorem is not invoked. Retained its statement dependencies
`FormalFunctionsFinitePullback`, `CoherentFormalModule`, and Mathlib's
`AlgebraicGeometry.IdealSheaf.Functorial`.
The following planned proof dependencies are unnecessary for this conditional lemma
(the definition nodes can still be needed to state it, and these modules may be needed
elsewhere; no claim of global unreachability):

- `def-nagata-extended-ideal` (`Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`).
- `def-pc-fibre-product` (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`).
- `def-pc-module-pullback` (`Sheaf.AlgebraicGeometry.TensorPullback`).
- `def-weil-pbc-coherent-formal-module` (`Sheaf.AlgebraicGeometry.CoherentFormalModule`).
- `def-weil-pbc-formal-functions-finite-pullback` (`Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback`).
- `lem-pc-module-pullback-adjunction` (`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`).
- `lem-weil-pbc-affine-morphism-cohomology-edge` (`Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge`).
- `lem-weil-pbc-closed-immersion-unit-quotient` (`Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`).
- `lem-weil-pbc-module-cohomology-fmap-basic-properties` (`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties`).
- `lem-weil-pbc-module-cohomology-fmap-functorial` (`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`).
- `lem-weil-pbc-module-pullback-quasi-coherent` (`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`).
- `lem-weil-pbc-quotient-base-change-closed-immersion-ideal` (`Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal`).
- `pqf-def-affine-morphism`.

## Where the brief, the DAG or earlier work was wrong

The DAG repeated the geometric construction of the quotient isomorphism, but the
Lean statement already assumes that isomorphism and its quotient-unit equation.
The only remaining task is linear-map composition. The unit's realized statement
and steps are unchanged: this helper is below the unit level.
The original import of FormalFunctionsFiniteQuotientIsoB had no compiled object in
the local green-build cache. It is unnecessary for this proof or its statement;
compilation succeeds with the actual statement dependencies instead.

Public-import pruning is recorded in
`coord/changes/formalFunctions_finite_quotient_iso_r_imports.md`.
The only direct importer, `FormalFunctionsFiniteQuotientIso` (unclaimed), imports
B independently and R privately. No forced adaptations or target reviews are needed.

## Earlier second reading (a previous round; superseded)

1. PASS: Diffed the sole delivered Lean module against the repository and
   mechanically compared the complete theorem signature byte for byte: identical.
   No definitions or declarations were added. The public-import replacement has
   its change record; a fresh whole-library import/use search confirms that the
   only downstream consumer is FormalFunctionsFiniteQuotientIso, which independently
   imports B. No target statement or meaning changes.
2. PASS: Independently compiled the delivered module through lcompile.py without
   errors or warnings. There is no sorry or forbidden declaration mechanism in it.
   A scratch copy with #print axioms reports propext, Classical.choice, Quot.sound,
   and sorryAx inherited from the existing unfinished imported theory. The proof
   constructs its witness directly by LinearMap.comp; it chooses no data from an
   unproved existence theorem and adds no axiom or hole.
3. PASS: No statements were split off and no new nodes or holes were added.
   Read both underlying ModuleCat morphisms and the supplied equation hb: their
   composition has exactly the required stalk-ring linear type. The argument also
   applies at n = 0, p = 0, zero F, and an empty fibre, since it uses only typed
   composition and the assumed component equation, with no cancellation or
   nonemptiness assumption.
4. PASS: Read the proof from the conclusion downward and checked Mathlib's
   ModuleCat.Hom.hom, ModuleCat.hom_comp, LinearMap.comp, and LinearMap.comp_apply.
   This is already the direct elementary route; no geometric comparison is needed
   to prove this conditional statement. All three public imports provide objects
   occurring in the unchanged signature; there are no proof-only public imports.
   Compared the old 13 proof_deps with No longer needed: every one is listed.
   Read dag/units/sk-thm-p1.json, including its statement, steps and realized
   fields: this helper realizes none of those steps, and pruning its redundant
   geometric proof plan changes no unit route. The parent still uses B to construct
   the isomorphism and then applies R to construct the linear maps.
5. PASS: Parsed and compared both node files. Only proof, proof_deps and
   proof_origin change as JSON values. The new elementary step describes precisely
   the Lean witness and the two formulas; proof_deps is correctly empty. The node
   statement, stmt_deps, Lean declaration record, source, chapter and unit remain
   unchanged. No new-node field requirements apply.

Second reading changed only this report, recording the independent checks above;
no proof or metadata repair was needed. Closed one hole, added zero holes, and
split off zero statements. Compilation and the explicit axiom probe were rerun by
this reader; delivery preflight follows.

## Second reading by C1

1. PASS. I diffed the delivered module against the repository version. The
   theorem signature and all existing declaration interfaces are unchanged. The
   only source differences are the documented import pruning, proof body, and
   proof docstring; the import change has its explicit change record.
2. PASS. The module and the complete sandbox import order compile with
   `lcompile.py` without errors or warnings. The module contains no `sorry`,
   forbidden declaration, or hollow definition. An axioms probe reports only
   the permitted foundational axioms plus `sorryAx` inherited from unfinished
   imported theory; this theorem introduces no new axiom.
3. PASS. The one target hole is closed and no holes or nodes are added. The
   witness is the typed composition of the two supplied ModuleCat linear maps,
   so the component equations are definitionally the first equation and exactly
   the hypothesis `hb` for the second. The construction remains valid in all
   degenerate cases because it uses no cancellation or nonemptiness assumption.
4. PASS. Reading downward from the conclusion, `LinearMap.comp` is the shortest
   route and no geometric theorem is needed. The three public imports are exactly
   the statement dependencies required by the unchanged signature; the former
   public import of `FormalFunctionsFiniteQuotientIsoB` is unused and is removed.
   Every removed proof dependency is listed under `No longer needed`, and the
   unit statement and realized route remain untouched.
5. PASS. The node statement, source, unit, chapter, and Lean declaration record
   agree with the source. Its proof has one elementary step with empty
   `proof_deps`, matching the composition proof in Lean; no new node or change to
   a target statement is present.

Changed only this report during second reading. No Lean proof, declaration,
signature, node statement, or DAG route required repair.
