# Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.Cohomology.Serre

## Reason

Repair the quarantined module's recorded namespace-closure error after the scheduled
upstream sync. The sync removed the public theorem declarations but left three local
`open ... in` commands immediately before `end AlgebraicGeometry`. These commands
consume the namespace closure inside anonymous scopes. The original file reproduces
`Unexpected name AlgebraicGeometry after end: The current section is unnamed`.

After the return at `1d9c9aac8f` for the stale delivery base `d92f73d8e`, read the
current shared and server copies, copied the current quarantined version afresh,
and reapplied this repair. The live module remains absent on both copies. The
current original fails in 2.9 seconds; the repaired version compiles cleanly in
2.5 seconds through the required remote single-file compiler.

This is a command-scope repair: no existing declaration signature, proof, definition
body, attribute or public import changes. The private helpers remain private. No
target statement or definition used by a target changes; no target review reopens.

## Old

The final commands of the quarantined module were:

```lean
variable {n} {X : Scheme.{u}} (k : Type u) [Field k]

open scoped AlgebraicGeometry.Scheme.Modules in
open scoped AlgebraicGeometry.Scheme.Modules in
open ProjectiveSpace in
end AlgebraicGeometry
```

## New

```lean
variable {n} {X : Scheme.{u}} (k : Type u) [Field k]

end AlgebraicGeometry
```

Additionally rewrap the current provenance comment verbatim to 100 columns and add the style
setting `set_option linter.privateModule false` before `noncomputable section`.
The module intentionally contains only the two retained private helpers. This setting
has no effect on proofs, visibility, kernel checking or downstream modules.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.Cohomology.Serre | T9 | Restored from quarantine; namespace closure compiles; public imports and declarations unchanged. |

`tools/downstream.py` reports the module unknown because it is quarantined. A search
for the module import across all live and quarantined Lean files found no users.
Searches for the helper names find only independent private declarations in other
upstream modules; those do not refer to these private helpers. No DAG node attaches
to this extra module, and no consumer requires adaptation.

## Status

landed 20261020T145540-L-2410277 2026-10-20 (merge of deliver/T9/Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.Cohomology.Serre)
