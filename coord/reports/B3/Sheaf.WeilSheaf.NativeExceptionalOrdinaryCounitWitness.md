## What changed

The assigned witness theorem now has a complete assembly proof. It imports two
proof-only modules: `Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitCarrier`, which
supplies the ordinary counit carrier and invariant equation, and
`Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitGraded`, which supplies the graded
bijections. The assigned node proof and `proof_deps` were updated to these two strict
substeps. Their declarations are intentionally the remaining named obligations.

## Proved and sorry left

The declaration `native_exceptional_ordinary_counit_witness` is proved by assembling
the carrier and graded conclusions in the unchanged target statement. Two sorries are
split off: `native_exceptional_ordinary_counit_carrier` (node
`lem-sf-native-exceptional-ordinary-counit-carrier`) and
`native_exceptional_ordinary_counit_graded` (node
`lem-sf-native-exceptional-ordinary-counit-graded`). No sorry occurs in a definition.

## No longer needed

The assigned theorem no longer directly cites the four original geometric proof
nodes; their roles are retained in the proof plans of the two split nodes. No import
was removed from the public interface. The two new modules are proof-only imports in
the assigned module.

## Where the brief, the DAG or earlier work was wrong

The original node left the carrier/invariance construction and the all-degree Hom
calculation as one unimplementable Lean obligation, while its proof text already
separated those arguments. The delivery makes that separation explicit as two
strictly smaller statements and proves the requested theorem by a genuine assembly.

## New nodes

`lem-sf-native-exceptional-ordinary-counit-carrier` records the fixed-comparison
ordinary counit carrier and its zero-shift invariant condition. Its module is
`Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitCarrier`.

`lem-sf-native-exceptional-ordinary-counit-graded` records the graded ordinary Hom
bijection for an already supplied carrier, with its transported-arrow and invariant
conditions as hypotheses. Its module is
`Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitGraded`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitCarrier": "fb6270c564098f04a50c5a335d01313dec994c64", "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitGraded": "95f9b1a6e1c5a4b4db865352370f39808acd2d82", "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness": "0e4c52d3e1311304c4ad0b61faf22e3ef3dbbb90"}, "results": {}, "time": "2026-10-28T09:09:57+0800", "transitive": 0, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
