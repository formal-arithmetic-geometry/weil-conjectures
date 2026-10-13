## What changed

The module now applies the split theorem `glued_model_chart_pullback_core` to construct the
`Nonempty (IsLimit ...)` component of `IsPullback`, then supplies the commutative-square
component. The existing target signature is unchanged. The core theorem remains a named
split-off hole because its stated hypotheses are insufficient.

## Proved and sorry left

The target theorem `CategoryTheory.Over.DescentDatum.glued_model_chart_pullback_single` is
reduced by a real application of `glued_model_chart_pullback_core`; its proof therefore still
depends on that split theorem. Sorry left: `CategoryTheory.Over.DescentDatum.glued_model_chart_pullback_core`,
with node `lem-pd-glued-effective-model-chart-pullback-single-core`. No new sorry was added.

## No longer needed

The previously delivered local commutativity helper and node were unused by the target proof
and were removed. No existing imports were removed.

## Where the brief, the DAG or earlier work was wrong

The chart-square conclusion is not implied by the listed hypotheses: an individual chart can
be empty while the other charts cover the glued model, so local cartesianness and an open
immersion do not force that individual square to be cartesian. The target retains its
`STATEMENT-DISPUTED` counterexample comment. The core declaration is likewise marked
`STATEMENT-DISPUTED`; a corrected statement needs an additional factorization or covering
condition on the selected chart.

## Second reading by T4

1. **Module comparison:** The target theorem's signature is byte-for-byte unchanged from the
repository version. The only proof change is the application of the named core theorem and the
square equation; the disputed-statement notice was restored.
2. **Proof and axioms:** The file compiles with `lcompile.py`; the only remaining `sorry` is the
named core theorem, and there are no definitions containing `sorry`, axioms, or unsafe features.
The target proof uses no unused helper.
3. **Statements and nodes:** The core split statement is exactly the intermediate result used by
the proof and is explicitly marked disputed because it is false under the given hypotheses. Its
node records the source, proof decomposition, and Lean declaration. The removed local helper had
no proof use and therefore needed no node.
4. **Pruning and imports:** No import is unused as a result of this proof. The proof follows the
unit route through the chart-square core step; no unit-level route was bypassed.
5. **DAG agreement:** The target node's proof and `proof_deps` point to the core node, and the
core node matches the remaining split theorem. No stale local-comm node remains.

## New nodes

`lem-pd-glued-effective-model-chart-pullback-single-core` is the split-off core theorem already
present in the delivery; it is stated in the existing module and remains open because the
hypotheses are insufficient.
