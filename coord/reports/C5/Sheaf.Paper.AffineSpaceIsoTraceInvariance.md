## What changed

Added the geometric core theorem `affineSpaceIsoTraceAction_eq_id`, which isolates the
stalkwise degree-one calculation for arbitrary affine-space isomorphisms. The target
now follows by rewriting the action to the identity and simplifying the identity
composition.

## Proved and sorry left

The target theorem `affineSpaceIsoTraceInvariance` is proved from
`affineSpaceIsoTraceAction_eq_id`. The new core theorem remains as one named `sorry`
whose proof is the geometric degree-one argument recorded in its docstring and node.

## No longer needed

None. The target still uses the affine linear trace-action definition and its declared
proof dependencies through the split-off geometric core.

## Where the brief, the DAG or earlier work was wrong

The blueprint proof describes a geometric fibre degree-one argument, but the existing
Lean API has no theorem expressing arbitrary nonlinear affine-space automorphism
invariance. The original target mixed that missing geometric result with the final
counit rewrite. The delivery separates them so the final theorem is a complete
categorical consequence of the missing core statement.

## New nodes

- `lem-pur-affine-space-iso-trace-action-id`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AffineSpaceIsoTraceCore": "92d9729fae0ebcad61f00e547639c917b7153e98", "Sheaf.Paper.AffineSpaceIsoTraceInvariance": "569bbf412f117cc8f128cd00c139d1b1bd5f9d7a"}, "results": {}, "time": "2026-10-28T07:57:29+0800", "transitive": 0, "version": 1}
```

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
