## What changed

Copied `Sheaf.Paper.PodReindexingStrictTensorTowers` into the A3 sandbox and replaced its
single proof hole with a real assembly proof. The proof obtains a strict tower
isomorphism and its pure tensor generator formula from
`podReindexingStrictTensorTowersGenerators`, then obtains the naturality square from
`podReindexingStrictTensorTowersNaturality`. Added those two strictly smaller public
statement modules, each retaining the corresponding unresolved construction as a named
stage-3 theorem with a documented source and proof plan. Updated the three DAG node
copies to record the decomposition and imports.

## Proved and sorry left

Proved `podReindexingStrictTensorTowers` (1 of 1 original sorry). Two strictly smaller
sorries remain: `podReindexingStrictTensorTowersGenerators` and
`podReindexingStrictTensorTowersNaturality`, one in each new module. No definitions contain
`sorry`.

## No longer needed

The original proof plan's direct dependencies
`lem-pod-reindexing-hom-resolution-model`, `lem-pur-kflat-change-of-rings`,
`lem-pur-kflat-total-tensor-model`, and `lem-pur-integral-operations-well-defined` are
used only by the two split interfaces, so the parent theorem imports no additional
modules beyond those interfaces. No declared dependency was pruned from the two
strictly smaller construction statements.

## Where the brief, the DAG or earlier work was wrong

The original item bundled the levelwise isomorphism, its generator equation, and
naturality into one construction too large to prove from the currently declared
interfaces. The DAG did not expose these independently. This delivery records the two
strictly smaller components explicitly and assembles them with a complete Lean proof;
the mathematical route and target statement are unchanged.

## New nodes

- `lem-pod-reindexing-strict-tensor-towers-generators`
- `lem-pod-reindexing-strict-tensor-towers-naturality`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingStrictTensorTowers": "cd49f56098365482d3c11a2399e5636de2918f3e", "Sheaf.Paper.PodReindexingStrictTensorTowersGenerators": "fc4748582ee245c227df284aafa4f30b9ddce261", "Sheaf.Paper.PodReindexingStrictTensorTowersNaturality": "99066df2bf45929e25d47b55cfb3ae4bc1395e0a"}, "results": {}, "time": "2026-10-28T07:57:51+0800", "transitive": 0, "version": 1}
```

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
