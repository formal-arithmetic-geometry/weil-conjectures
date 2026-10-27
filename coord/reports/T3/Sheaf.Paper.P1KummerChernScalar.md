## What changed

Proved `AlgebraicGeometry.Etale.p1KummerChernScalar` by reducing it to the
ordinary class transport and Kummer normalization identities supplied by two
new intermediate theorem modules. Added the explicit underlying additive map
of a normalized Tate-line insertion.

## Proved and sorry left

The target `p1KummerChernScalar` is proved. Two strictly smaller transport
lemmas remain as named `sorry`s:
`p1KummerChernScalar_class_transport` and
`p1KummerChernScalar_kummer_transport`.

## No longer needed

No declared dependency was pruned. The endpoint record remains the statement
interface, and the generic Ext-composition comparison is used by the new class
transport node.

## Where the brief, the DAG or earlier work was wrong

The current global build error reported a bad import for the endpoint module,
but the endpoint chain compiles against the published artifacts in the sandbox.
The item proof plan omitted the explicit underlying additive comparison between
restriction of scalars and B-coefficient forgetting; the new definition records
that comparison.

## New nodes

- `lem-sp-p1-kummer-chern-class-transport`
- `lem-sp-p1-kummer-chern-kummer-transport`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.P1KummerChernScalar": "1bdcd2089b633020046fe37cf37fe342b1c0659d", "Sheaf.Paper.P1KummerChernScalarClassTransport": "1aa87a371ffa344c38dbe761e9448a4902db2c97", "Sheaf.Paper.P1KummerChernScalarKummerTransport": "a412107cf429010e6a2a64f6539d38924c99f057"}, "results": {}, "time": "2026-10-28T03:44:38+0800", "transitive": 0, "version": 1}
```

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
