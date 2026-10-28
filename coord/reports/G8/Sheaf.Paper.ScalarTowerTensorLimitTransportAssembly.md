## What changed

The assigned theorem
\`WeilConjectures.ScalarExtensionTower.scalarTowerTensorLimitSquare_of_strictWitnesses\`
is proved by extracting a \`DerivedSigmaModel\` family from each
\`StrictTensorWitness\`, then applying two explicit transport stages.  The first
new module records the realized equality on K-flat good localization
representatives, including an explicit bridge from scalar extension of the E
tensor to the completed L tensor.  The second records the localization,
completion, and total-limit assembly from that representative family.

The original hP and hQ binder names are restored in the item declaration and
its DAG Lean record.  The duplicate \`StrictSigmaEquationFor\` definition is
removed.

## Proved and sorry left

Closed 1 sorry:
\`scalarTowerTensorLimitSquare_of_strictWitnesses\`.

Added 2 strictly smaller named transport sorries:
\`scalarTowerTensorLimitSquare_on_good_representatives\` records the
K-flat representative, SY/TL normalization, and naturality calculation.
\`scalarTowerTensorLimitSquare_of_representativeTransport\` records the
localization, completion, and total-limit functoriality step.

No definition contains a sorry.

## No longer needed

The duplicate module declaration and DAG node
\`stage3-pur-scalar-tensor-limit-strict-equation-predicate\` are no longer
needed: its predicate was definitionally the existing \`DerivedSigmaModel\`
and supplied no independent argument.  The old \`hEq\` route through that
predicate is pruned.  The strict-witness module remains needed for the
witness extraction in the item proof.

## Where the brief, the DAG or earlier work was wrong

The returned review correctly identified that the former strict-equation
theorem merely renamed \`DerivedSigmaModel\` and therefore did not prove
transport.  The repair separates the genuinely different representative
calculation from the later localization/completion/total-limit assembly.
The item node's previous Lean statement also had stale underscore-prefixed
binder names; the declaration and node now use the original hP and hQ names.

## New nodes

\`stage3-pur-scalar-tensor-limit-good-representatives\` records the strict
representative transport theorem in
\`lean/Sheaf/Paper/ScalarTowerTensorLimitRepresentativeTransport.lean\`.

\`stage3-pur-scalar-tensor-limit-strict-equation-assembly\` now records the
localization/completion/total-limit theorem in
\`lean/Sheaf/Paper/ScalarTowerTensorLimitStrictEquationAssembly.lean\`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ScalarTowerTensorLimitRepresentativeTransport": "e0768c8e26a202f2e21b2c36f1095a69021c46a4", "Sheaf.Paper.ScalarTowerTensorLimitStrictEquationAssembly": "2711e16ae2182b7ff263b2fb6b34691edebc77ba", "Sheaf.Paper.ScalarTowerTensorLimitTransportAssembly": "852ed0565aa9cc152bba17a7f1cbc31a07ff28bd"}, "results": {}, "time": "2026-10-28T08:45:52+0800", "transitive": 0, "version": 1}
```

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
