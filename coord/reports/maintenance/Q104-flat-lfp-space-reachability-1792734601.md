# Q104 flat/lfp algebraic-space openness: maintenance resolution

The retained stage-2 packet for `lem-sfb-flat-lfp-space-universally-open`
now passes normal delivery preflight and the full landing graph validator.

The original L return on immutable head `90b473dc935d` was accurate: against
its merge base `fd440e6ee1ee84085765caaa74634e3ecfad7abe`, the actual
`nt_incremental2.check` returns exactly:

```
reach: def-sfb-space-morphism-properties is not reached from a target and is not flagged unreachable
```

The worker added the requested unreachable flag, but `stage2_delivery.py`
rejects `import_flags` on a new stage-2 definition node because the field is
maintainer-owned. Repeated retries preserved that packet and treated the old
return as a current requirement. Compilation succeeded; preflight refused
the same field. This was a metadata ownership conflict, not mathematics or
a compiler/provider failure.

The current graph has since changed. At `28286a91dea90623f9045e78e6a31530fdb4e504`,
the item is reached from `nt-target-zeta-rational`, through the trace/ctf route,
the tame-pair lattice and alteration route, stable pointed-curve extension,
unpointed coarse projectivity, and `lem-sfb-nodal-curve-stack-smooth`.
Several of those edges/nodes were absent or unsplit at the old base.
The helper is reached when the packet adds its existing `stmt_deps` edge.
Keeping the flag now produces a stale-flag global finding; removing it gives
no related global finding and `nt_incremental2.check` returns `[]`.

Maintenance changed only the retained sandbox helper JSON by removing
`import_flags: ["unreachable"]` and prepended the current explanation to
its `report.md`. Both files have adjacent
`.maint-Q104-flat-lfp-space-1792734601.bak` backups. All Lean source bytes,
signatures, item content, mathematical/search/source records, and dependency
edges are unchanged. No DAG prerequisite or Lean binding was pre-landed.
The helper remains a NEW definition node of the normal stage-2 delivery.
No delivery, landing, review, dispatcher, or admission tool was modified.

Validation:

- Unchanged `deliver2.py Q104 lem-sfb-flat-lfp-space-universally-open --no-push`
  succeeded at candidate `d2a0982fa8d`; compilation and preflight passed.
- Read-only simulation of the owned delivery fields on the current server
  DAG passed the actual landing validator, `nt_incremental2.check`: `[]`.
- Both unchanged files separately passed `tools/lean_file.sh`, sequentially,
  in a private source/artifact view over the normal published build and
  compiler cache: `AlgebraicSpaceMorphismProperties.lean` 4.9 seconds,
  `AlgebraicSpaceFlatLfpUniversallyOpen.lean` 2.5 seconds. Limit: 60 seconds.

Next worker: resume the retained Q104 packet on current `sheaf-dag`, keep
the helper as a new node without the obsolete flag, retain both modules and
the item's added dependency, run the normal dry run, and deliver for normal
independent review. Historical BLOCKED appendices and the immutable-head
return concern the old graph. Do not restore the flag or restart mathematics.
Maintenance did not clear the return/claim, push a delivery, or approve stage 2.

Protected-tool follow-up for the owners: new helpers below an unreachable
parent need maintainer-assigned reachability metadata before landing; returning
that field edit to a worker conflicts with new-node ownership. The dry run's
`nt_preflight2.graph_findings` calls only `nt_incremental2.local_findings`,
while landing also compares global findings; align those checks while retaining
ownership and accurate reachability validation. Those tools are unchanged.
