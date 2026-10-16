## What changed

Moved `exists_nonempty_support_open_closed_models` into
`Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed` and
`glue_nonempty_support_open_closed_models` into
`Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing`, preserving their
signatures and proofs (`sorry`). The item imports those two helper modules and
combines them to prove `exists_finiteCoefficient_model_on_closed_support_step_nonempty`.
Removed the unused `ProEtaleModuleConstructiblePullback` import. Updated all three
DAG nodes with the helper module paths, complete statements, proof descriptions,
and the target's actual two-step proof route.

## Proved and sorry left

`AlgebraicGeometry.ProEtale.exists_finiteCoefficient_model_on_closed_support_step_nonempty`
is proved by applying the two helper declarations and installing the immersion
instances. Two named `sorry`s remain:

- `AlgebraicGeometry.ProEtale.exists_nonempty_support_open_closed_models` (node
  `new-lem-weil-pbc-condensed-stratum-model-induction-step-nonempty-open-closed`).
- `AlgebraicGeometry.ProEtale.glue_nonempty_support_open_closed_models` (node
  `new-lem-weil-pbc-condensed-stratum-model-induction-step-nonempty-gluing`).

## No longer needed

The item no longer imports the former proof-only imports. The helper modules retain
only their public imports needed by the theorem signatures; all copied plain imports,
including `Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`, were removed.
No DAG node or module is unused by the target route.

## Where the brief, the DAG or earlier work was wrong

The returned delivery had both intermediate declarations in the item module and
recorded incomplete node statements and proof steps. The declarations are now in
separate modules, and the helper node statements describe every hypothesis and
witness of their exact Lean signatures. The target node now records the actual
helper-application proof and its two dependencies.

## New nodes

`new-lem-weil-pbc-condensed-stratum-model-induction-step-nonempty-open-closed` is
implemented by
`lean/Sheaf/Paper/CondensedStratumModelInductionStepNonemptyOpenClosed.lean`.
`new-lem-weil-pbc-condensed-stratum-model-induction-step-nonempty-gluing` is
implemented by
`lean/Sheaf/Paper/CondensedStratumModelInductionStepNonemptyGluing.lean`.
The existing interface change record is
`coord/changes/nonempty-support-interfaces.md`.

## Earlier second reading (a previous round; superseded)

1. **Interfaces and signatures: PASS.** Compared the delivered target module with the
repository version. The target theorem statement is unchanged byte for byte. The two
new helper declarations have complete signatures and are strict reductions of the target;
no target or existing declaration was weakened. The change record documents the new
helper modules and their sole importer.

2. **Compilation and proof integrity: PASS.** Compiled all three delivered modules with
`python3 /home/ubuntu/weil-launcher/lcompile.py --all ...`; all compiled successfully.
The target proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or
`extern`. The only remaining `sorry`s are the two named split-off helper theorems, each
with a docstring, node, and source. I also removed the two docstring long-line warnings.

3. **Statements and split nodes: PASS.** Read both helper statements and their DAG
records against the Lean declarations. The open/closed theorem supplies the geometric
decomposition data; the gluing theorem consumes exactly that data and returns the target
conclusion. Neither restates the item, and both are true, needed intermediate claims.

4. **DAG, imports, and pruning: PASS.** The target proof uses exactly the two helper
declarations and installs the immersion instances they require. The helper modules expose
only their signature imports; removed proof-only imports are recorded under “No longer
needed”. The node proof routes and dependencies match the delivered declarations, and the
`sk-thm-properbasechange` unit route is retained.

5. **Delivery readiness: PASS.** No accidental edits to repository files or unrelated
modules were found. The required report, change record, helper nodes, and modules are
present. The only change made during this reading was wrapping the two long docstring
lines; no mathematical interface or proof route changed.

## Second reading by F3

1. **Interfaces and signatures: PASS.** I compared the target module with the
repository version. Its theorem signature is unchanged byte for byte. The two helper
theorems have exact, complete signatures and each supplies a strict intermediate part
of the target argument; no existing target or declaration was weakened.

2. **Compilation and proof integrity: PASS.** All three modules compile with
`python3 /home/ubuntu/weil-launcher/lcompile.py --all ...`. The target proof has no
`sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The only open
holes are the two named helper theorems, each documented and represented by a DAG node;
the target's `sorryAx` dependency is therefore solely through those open nodes.

3. **Statements and split nodes: PASS.** I checked both helper declarations against
their Lean files and DAG records. The open/closed helper constructs complementary
immersions and models, while the gluing helper consumes precisely those witnesses and
returns the target conclusion. Neither helper restates the target.

4. **DAG, imports, and pruning: PASS.** The target proof uses exactly the two helper
declarations and installs the required immersion instances. The helper modules expose
only imports needed by their signatures; removed proof-only imports are recorded under
“No longer needed”. Node proof routes and dependencies match the Lean proof, and the
`sk-thm-properbasechange` unit route remains represented.

5. **Delivery readiness: PASS.** I found no unrelated file edits or accidental
signature changes. The required report, change record, helper modules, and helper DAG
nodes are present. I changed only this report section during this reading, adding the
required exact heading and five-point verdicts.
