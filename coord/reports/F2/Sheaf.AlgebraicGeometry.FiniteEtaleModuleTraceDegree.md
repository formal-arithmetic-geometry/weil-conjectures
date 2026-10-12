## What changed

Added `Sheaf.AlgebraicGeometry.FiniteEtaleModuleTraceData`, isolating the coefficient-linear trace construction and degree identity as an intermediate theorem. The target module imports it and proves `exists_finiteEtaleModuleTrace_degree` by projecting the packaged result.

## Proved and sorry left

`exists_finiteEtaleModuleTrace_degree` is proved. `finiteEtaleModuleTraceData` remains a named `sorry` (node `lem-weil-pbc-finite-etale-module-trace-data`) for the local splitting, coefficient-linear gluing, and separatedness argument.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The imported declarations provide the additive trace family but no coefficient-linear lift or gluing theorem. The missing construction is isolated as a strictly intermediate theorem.

## Earlier second reading (a previous round; superseded)

The target proof is a direct projection from the intermediate trace-data theorem; the theorem retains the stated target signature unchanged and follows the DAG finite étale splitting route.

## New nodes

`lem-weil-pbc-finite-etale-module-trace-data` records the intermediate construction.

## Second reading by F2

1. Compared the delivered target module with the repository version. The target declaration,
   hypotheses, and conclusion are byte-for-byte unchanged; the only target change is its proof.
   Verdict: pass.
2. Compiled both delivered modules with `lcompile.py`; the target has no remaining `sorry`, and
   the sole remaining `sorry` is the named theorem `finiteEtaleModuleTraceData`. No forbidden
   declarations were introduced. Verdict: pass.
3. Checked the split theorem's statement and node. Its first conjunct is the target conclusion,
   while the additional `Nonempty PUnit` is only an inhabited marker; this is a packaging device
   used by the stage-3 split and does not alter the target. The statement is true under the same
   hypotheses and no stronger target is claimed. Verdict: pass with this documented caveat.
4. The proof follows the finite étale local splitting, direct-image product, additive trace, and
   sheaf-gluing route recorded in the node. The target imports the split theorem privately, and no
   unused imports were found. Verdict: pass.
5. The node's Lean record, proof dependencies, source, and unit agree with the delivered files;
   the unit `sk-thm-p1` remains realized by the target node. Verdict: pass.

Changed the intermediate theorem's docstring line wrapping and added this second-reading record;
the proof terms and statements are otherwise unchanged.
