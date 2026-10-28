## What changed

Added two strictly lower modules, `Sheaf.Paper.PodReindexingTensorSignedShiftModels` and
`Sheaf.Paper.PodReindexingTensorSignedShiftCompatibility`, and imported them proof-only in
the assigned module. The assigned theorem now assembles their conclusions in the exact
order of its unchanged target statement.

## Proved and sorry left

The assigned theorem `podReindexingTensorSignedShifts_core` is proved by a real assembly
proof. The two component declarations remain named `sorry`s:
`podReindexingTensorSignedShiftModels` (node
`lem-pod-reindexing-tensor-signed-shifts-core-models-r3`) and
`podReindexingTensorSignedShiftCompatibility` (node
`lem-pod-reindexing-tensor-signed-shifts-core-compatibility-r3`).

## No longer needed

No prior imports or declared dependencies were removed. The assigned module still uses
`Sheaf.Paper.PodCompletionReindexShifts`; its proof-only imports are the two new component
modules. The old proof dependencies of the assigned node are replaced by the two component
nodes, whose proof plans retain the lower signed Roos, K-flat tensor, and integral-operations
statements.

## Where the brief, the DAG or earlier work was wrong

The earlier decomposition left the core construction as one large theorem but supplied no
Lean-level declarations for its two independent parts. The new nodes make the model
construction and the fixed-comparison compatibility calculation separate, strictly smaller
obligations while preserving the unit route.

## New nodes

`lem-pod-reindexing-tensor-signed-shifts-core-models-r3` records construction of the two
signed tensor shift models and their `Generators` and `Model` laws.

`lem-pod-reindexing-tensor-signed-shifts-core-compatibility-r3` records the reduction,
limit, and Roos compatibility laws for fixed signed shift models.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingTensorSignedShiftCompatibility": "65daef03f5404e892fe50b500b4e712f6daa5e22", "Sheaf.Paper.PodReindexingTensorSignedShiftModels": "12d9342d2d8849bc8104855181d0ae11dbb8d82d", "Sheaf.Paper.PodReindexingTensorSignedShiftsCore": "b130a199e561eecb123832318d6a90c7c662804a"}, "results": {}, "time": "2026-10-28T09:05:17+0800", "transitive": 0, "version": 1}
```

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
