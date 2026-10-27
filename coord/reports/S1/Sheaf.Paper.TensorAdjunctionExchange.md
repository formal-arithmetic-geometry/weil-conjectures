## What changed

Repaired the coefficient-shift conclusion in the assigned module. The old
CorePackage.coefficientShifts quantified over arbitrary Change records whose
tensor comparison natural isomorphisms need not respect shifts. The new
CoefficientComparisons record retains all four specified coefficient witnesses
and requires the same witnesses to carry the five actual ChangeShifts squares.
The detailed parity counterexample and source comparison are in
coord/changes/S1-tensor-adjunction-coefficient-shifts.md.

This is a definition repair, not a proof of tensor_adjunction. The theorem's
binder list, conclusion text, proof hole and full proof docstring are preserved.
No target or adopted WeilConjectures source is edited. The existing DAG node
keeps its mathematical statement and proof route; its declaration list records
the two new definitions belonging to the same notion.

The initial direct implementation timed out while elaborating the enlarged
CorePackage. Factoring the coefficient witnesses into their own dependent
record and making the existing universes explicit fixes the cause without
raising any resource limit or splitting a proof to evade the limit.

## Proved and sorry left

Holes closed: 0 of 1. Holes added: 0. Split off: 0.
The remaining hole is
WeilConjectures.TensorAdjunctionExchange.tensor_adjunction
(node fix-lem-tensor-adjunction), unchanged. Both new definitions contain zero
holes. The actual repair is the corrected quantifier and retained shift evidence
for all four canonical coefficient maps, not a compiling no-op.

## No longer needed

No imports, mathematical nodes or library modules are pruned. No declaration
from the adopted source tree is removed. The original universal shift claim for
arbitrary unnormalized tensor comparisons is removed because it is false;
finite reduction, integral extension, rationalization, rational extension and
common inclusion retain their shift squares on the very same normalized maps.

A generic five-bijection Yoneda argument was developed and compiled successfully
in scratchpad/TensorAdjunctionYoneda.lean. It is not imported or delivered: the
current definition repair does not need a new theorem node or that extra module.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (repaired): Change imposes projection compatibility but no
shift compatibility on tensorX or tensorY. At the identity geometric point with
F_3 coefficients, parity on the tensor output gives a Change whose Hom map for
the tensor unit is parity on N. It anticommutes with the canonical second Hom
shift. Consequently CorePackage.coefficientShifts as formerly quantified is
false. The blueprint's stated coefficient maps are normalized maps, so the
correct definition places the shift evidence on those specified witnesses.

The downstream.py audit finds no live downstream Lean modules. The six DAG
citers and quarantined consumers were checked; each uses the canonical exchange
and keeps the same meaning, so no consumer needs adaptation. The change record
names them individually. The unchanged target statement must be reviewed with
this corrected underlying definition.

The recorded signed-transpose dependency source
Sheaf.SixFunctors.TensorHomSignedTransposes is absent from both the live tree
and quarantine, with no rework row found. This repair does not recreate it,
withdraw it or remove its dependency edge.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
